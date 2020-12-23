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
% DateTime   : Thu Dec  3 11:09:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 308 expanded)
%              Number of clauses        :   31 ( 104 expanded)
%              Number of leaves         :   14 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  235 (1377 expanded)
%              Number of equality atoms :   87 ( 139 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(t47_orders_2,axiom,(
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
                  & r2_hidden(X2,k1_orders_2(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ~ r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t48_orders_2])).

fof(c_0_15,plain,(
    ! [X67,X68] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X67),X68),X67)
        | ~ m1_subset_1(X68,u1_struct_0(X67))
        | v2_struct_0(X67)
        | ~ v3_orders_2(X67)
        | ~ l1_orders_2(X67) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X67),X68),k1_zfmisc_1(u1_struct_0(X67)))
        | ~ m1_subset_1(X68,u1_struct_0(X67))
        | v2_struct_0(X67)
        | ~ v3_orders_2(X67)
        | ~ l1_orders_2(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r2_hidden(esk3_0,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X63,X64] :
      ( v2_struct_0(X63)
      | ~ v3_orders_2(X63)
      | ~ v4_orders_2(X63)
      | ~ v5_orders_2(X63)
      | ~ l1_orders_2(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | m1_subset_1(k1_orders_2(X63,X64),k1_zfmisc_1(u1_struct_0(X63))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X60,X61,X62] :
      ( ~ r2_hidden(X60,X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(X62))
      | ~ v1_xboole_0(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X65,X66] :
      ( v1_xboole_0(X65)
      | ~ m1_subset_1(X66,X65)
      | k6_domain_1(X65,X66) = k1_tarski(X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_29,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38) = k5_enumset1(X32,X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20]),c_0_26]),c_0_27]),c_0_21])]),c_0_22])).

fof(c_0_38,plain,(
    ! [X69,X70,X71] :
      ( v2_struct_0(X69)
      | ~ v3_orders_2(X69)
      | ~ v4_orders_2(X69)
      | ~ v5_orders_2(X69)
      | ~ l1_orders_2(X69)
      | ~ m1_subset_1(X70,u1_struct_0(X69))
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X69)))
      | ~ r2_hidden(X70,X71)
      | ~ r2_hidden(X70,k1_orders_2(X69,X71)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_orders_2])])])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk3_0,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_orders_2(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58] :
      ( ( ~ r2_hidden(X48,X47)
        | X48 = X39
        | X48 = X40
        | X48 = X41
        | X48 = X42
        | X48 = X43
        | X48 = X44
        | X48 = X45
        | X48 = X46
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X39
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X40
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X41
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X42
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X43
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X44
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X45
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( X49 != X46
        | r2_hidden(X49,X47)
        | X47 != k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X50
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X51
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X52
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X53
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X54
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X55
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X56
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) != X57
        | ~ r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) )
      & ( r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X50
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X51
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X52
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X53
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X54
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X55
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X56
        | esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58) = X57
        | X58 = k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_25]),c_0_20]),c_0_26]),c_0_27]),c_0_21])]),c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_19]),c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_orders_2(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_0,k1_orders_2(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_19]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t48_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 0.13/0.38  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 0.13/0.38  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 0.13/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(t47_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k1_orders_2(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 0.13/0.38  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), inference(assume_negation,[status(cth)],[t48_orders_2])).
% 0.13/0.38  fof(c_0_15, plain, ![X67, X68]:((v6_orders_2(k6_domain_1(u1_struct_0(X67),X68),X67)|~m1_subset_1(X68,u1_struct_0(X67))|(v2_struct_0(X67)|~v3_orders_2(X67)|~l1_orders_2(X67)))&(m1_subset_1(k6_domain_1(u1_struct_0(X67),X68),k1_zfmisc_1(u1_struct_0(X67)))|~m1_subset_1(X68,u1_struct_0(X67))|(v2_struct_0(X67)|~v3_orders_2(X67)|~l1_orders_2(X67)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&r2_hidden(esk3_0,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X63, X64]:(v2_struct_0(X63)|~v3_orders_2(X63)|~v4_orders_2(X63)|~v5_orders_2(X63)|~l1_orders_2(X63)|~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|m1_subset_1(k1_orders_2(X63,X64),k1_zfmisc_1(u1_struct_0(X63)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_23, plain, ![X60, X61, X62]:(~r2_hidden(X60,X61)|~m1_subset_1(X61,k1_zfmisc_1(X62))|~v1_xboole_0(X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.38  cnf(c_0_24, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_28, plain, ![X65, X66]:(v1_xboole_0(X65)|~m1_subset_1(X66,X65)|k6_domain_1(X65,X66)=k1_tarski(X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.38  fof(c_0_29, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_30, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_31, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_32, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_33, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_34, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_35, plain, ![X32, X33, X34, X35, X36, X37, X38]:k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38)=k5_enumset1(X32,X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20]), c_0_26]), c_0_27]), c_0_21])]), c_0_22])).
% 0.13/0.38  fof(c_0_38, plain, ![X69, X70, X71]:(v2_struct_0(X69)|~v3_orders_2(X69)|~v4_orders_2(X69)|~v5_orders_2(X69)|~l1_orders_2(X69)|(~m1_subset_1(X70,u1_struct_0(X69))|(~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X69)))|(~r2_hidden(X70,X71)|~r2_hidden(X70,k1_orders_2(X69,X71)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_orders_2])])])])).
% 0.13/0.38  cnf(c_0_39, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk3_0,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_49, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,X3)|~r2_hidden(X2,k1_orders_2(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_50, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.38  fof(c_0_52, plain, ![X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58]:(((~r2_hidden(X48,X47)|(X48=X39|X48=X40|X48=X41|X48=X42|X48=X43|X48=X44|X48=X45|X48=X46)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))&((((((((X49!=X39|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))&(X49!=X40|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X41|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X42|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X43|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X44|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X45|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X46|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))))&(((((((((esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X50|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X51|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X52|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X53|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X54|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X55|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X56|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X57|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X50|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X51|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X52|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X53|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X54|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X55|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X56|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X57)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_25]), c_0_20]), c_0_26]), c_0_27]), c_0_21])]), c_0_22])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_19]), c_0_51])).
% 0.13/0.38  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_orders_2(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_54])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_0,k1_orders_2(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[c_0_48, c_0_54])).
% 0.13/0.38  cnf(c_0_58, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_19]), c_0_58])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 60
% 0.13/0.38  # Proof object clause steps            : 31
% 0.13/0.38  # Proof object formula steps           : 29
% 0.13/0.38  # Proof object conjectures             : 19
% 0.13/0.38  # Proof object clause conjectures      : 16
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 14
% 0.13/0.38  # Proof object generating inferences   : 7
% 0.13/0.38  # Proof object simplifying inferences  : 32
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 14
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 38
% 0.13/0.38  # Removed in clause preprocessing      : 7
% 0.13/0.38  # Initial clauses in saturation        : 31
% 0.13/0.38  # Processed clauses                    : 86
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 77
% 0.13/0.38  # Other redundant clauses eliminated   : 17
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 9
% 0.13/0.38  # Generated clauses                    : 41
% 0.13/0.38  # ...of the previous two non-trivial   : 49
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 32
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 17
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 28
% 0.13/0.38  #    Positive orientable unit clauses  : 18
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 8
% 0.13/0.38  # Current number of unprocessed clauses: 20
% 0.13/0.38  # ...number of literals in the above   : 61
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 47
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 104
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 62
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 5
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 58
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4107
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.028 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

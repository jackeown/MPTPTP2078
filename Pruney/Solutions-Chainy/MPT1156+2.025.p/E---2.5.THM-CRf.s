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
% DateTime   : Thu Dec  3 11:09:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 117 expanded)
%              Number of clauses        :   33 (  43 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  236 ( 449 expanded)
%              Number of equality atoms :   87 ( 108 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_16,plain,(
    ! [X69,X70] :
      ( v1_xboole_0(X69)
      | ~ m1_subset_1(X70,X69)
      | k6_domain_1(X69,X70) = k1_tarski(X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_17,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38) = k5_enumset1(X32,X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,negated_conjecture,(
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

fof(c_0_25,plain,(
    ! [X71,X72,X73] :
      ( v2_struct_0(X71)
      | ~ v3_orders_2(X71)
      | ~ v4_orders_2(X71)
      | ~ v5_orders_2(X71)
      | ~ l1_orders_2(X71)
      | ~ m1_subset_1(X72,u1_struct_0(X71))
      | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X71)))
      | ~ r2_hidden(X72,X73)
      | ~ r2_hidden(X72,k2_orders_2(X71,X73)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_orders_2])])])])).

fof(c_0_26,plain,(
    ! [X64,X65,X66] :
      ( ~ r2_hidden(X64,X65)
      | ~ m1_subset_1(X65,k1_zfmisc_1(X66))
      | m1_subset_1(X64,X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_27,plain,(
    ! [X60,X61] :
      ( ~ r2_hidden(X60,X61)
      | m1_subset_1(k1_tarski(X60),k1_zfmisc_1(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k2_orders_2(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
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

fof(c_0_43,plain,(
    ! [X62,X63] :
      ( ~ m1_subset_1(X62,X63)
      | v1_xboole_0(X63)
      | r2_hidden(X62,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k2_orders_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X67] :
      ( v2_struct_0(X67)
      | ~ l1_struct_0(X67)
      | ~ v1_xboole_0(u1_struct_0(X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,k2_orders_2(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57])]),c_0_58]),c_0_59])).

fof(c_0_62,plain,(
    ! [X68] :
      ( ~ l1_orders_2(X68)
      | l1_struct_0(X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:12:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.036 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.39  fof(t50_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 0.19/0.39  fof(t49_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k2_orders_2(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 0.19/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.39  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.19/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.39  fof(c_0_16, plain, ![X69, X70]:(v1_xboole_0(X69)|~m1_subset_1(X70,X69)|k6_domain_1(X69,X70)=k1_tarski(X70)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.39  fof(c_0_17, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_18, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_19, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_20, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  fof(c_0_21, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.39  fof(c_0_22, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.39  fof(c_0_23, plain, ![X32, X33, X34, X35, X36, X37, X38]:k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38)=k5_enumset1(X32,X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.39  fof(c_0_24, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), inference(assume_negation,[status(cth)],[t50_orders_2])).
% 0.19/0.39  fof(c_0_25, plain, ![X71, X72, X73]:(v2_struct_0(X71)|~v3_orders_2(X71)|~v4_orders_2(X71)|~v5_orders_2(X71)|~l1_orders_2(X71)|(~m1_subset_1(X72,u1_struct_0(X71))|(~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X71)))|(~r2_hidden(X72,X73)|~r2_hidden(X72,k2_orders_2(X71,X73)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_orders_2])])])])).
% 0.19/0.39  fof(c_0_26, plain, ![X64, X65, X66]:(~r2_hidden(X64,X65)|~m1_subset_1(X65,k1_zfmisc_1(X66))|m1_subset_1(X64,X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.39  fof(c_0_27, plain, ![X60, X61]:(~r2_hidden(X60,X61)|m1_subset_1(k1_tarski(X60),k1_zfmisc_1(X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.39  cnf(c_0_28, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  fof(c_0_36, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.19/0.39  cnf(c_0_37, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,X3)|~r2_hidden(X2,k2_orders_2(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_38, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_39, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_40, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  fof(c_0_42, plain, ![X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58]:(((~r2_hidden(X48,X47)|(X48=X39|X48=X40|X48=X41|X48=X42|X48=X43|X48=X44|X48=X45|X48=X46)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))&((((((((X49!=X39|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))&(X49!=X40|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X41|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X42|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X43|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X44|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X45|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)))&(X49!=X46|r2_hidden(X49,X47)|X47!=k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46))))&(((((((((esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X50|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X51|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X52|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X53|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X54|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X55|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X56|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)!=X57|~r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))&(r2_hidden(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58),X58)|(esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X50|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X51|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X52|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X53|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X54|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X55|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X56|esk1_9(X50,X51,X52,X53,X54,X55,X56,X57,X58)=X57)|X58=k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.19/0.39  fof(c_0_43, plain, ![X62, X63]:(~m1_subset_1(X62,X63)|(v1_xboole_0(X63)|r2_hidden(X62,X63))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.39  cnf(c_0_44, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k2_orders_2(X1,X2))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.39  cnf(c_0_45, plain, (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_49, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  fof(c_0_50, plain, ![X67]:(v2_struct_0(X67)|~l1_struct_0(X67)|~v1_xboole_0(u1_struct_0(X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.39  cnf(c_0_51, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,k2_orders_2(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))|~r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))|~r2_hidden(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_57, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_41])).
% 0.19/0.39  cnf(c_0_60, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57])]), c_0_58]), c_0_59])).
% 0.19/0.39  fof(c_0_62, plain, ![X68]:(~l1_orders_2(X68)|l1_struct_0(X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_58])).
% 0.19/0.39  cnf(c_0_64, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_56])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 66
% 0.19/0.39  # Proof object clause steps            : 33
% 0.19/0.39  # Proof object formula steps           : 33
% 0.19/0.39  # Proof object conjectures             : 16
% 0.19/0.39  # Proof object clause conjectures      : 13
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 22
% 0.19/0.39  # Proof object initial formulas used   : 16
% 0.19/0.39  # Proof object generating inferences   : 7
% 0.19/0.39  # Proof object simplifying inferences  : 28
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 16
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 39
% 0.19/0.39  # Removed in clause preprocessing      : 7
% 0.19/0.39  # Initial clauses in saturation        : 32
% 0.19/0.39  # Processed clauses                    : 107
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 10
% 0.19/0.39  # ...remaining for further processing  : 97
% 0.19/0.39  # Other redundant clauses eliminated   : 17
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 2
% 0.19/0.39  # Backward-rewritten                   : 4
% 0.19/0.39  # Generated clauses                    : 112
% 0.19/0.39  # ...of the previous two non-trivial   : 94
% 0.19/0.39  # Contextual simplify-reflections      : 2
% 0.19/0.39  # Paramodulations                      : 103
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 17
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 50
% 0.19/0.39  #    Positive orientable unit clauses  : 15
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 33
% 0.19/0.39  # Current number of unprocessed clauses: 51
% 0.19/0.39  # ...number of literals in the above   : 225
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 45
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 310
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 236
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.39  # Unit Clause-clause subsumption calls : 37
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 57
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 5176
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.048 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.052 s
% 0.19/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

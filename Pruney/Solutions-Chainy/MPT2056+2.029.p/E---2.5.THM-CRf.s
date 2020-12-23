%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:55 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 616 expanded)
%              Number of clauses        :   70 ( 272 expanded)
%              Number of leaves         :   16 ( 157 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 (1751 expanded)
%              Number of equality atoms :   68 ( 556 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t15_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t14_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(t2_yellow19,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_16,plain,(
    ! [X36,X37] : k1_setfam_1(k2_tarski(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,X31)
        | ~ r2_hidden(X30,k4_xboole_0(X31,k1_tarski(X32))) )
      & ( X30 != X32
        | ~ r2_hidden(X30,k4_xboole_0(X31,k1_tarski(X32))) )
      & ( ~ r2_hidden(X30,X31)
        | X30 = X32
        | r2_hidden(X30,k4_xboole_0(X31,k1_tarski(X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t15_yellow19])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ( ~ r1_xboole_0(X26,X27)
        | k4_xboole_0(X26,X27) = X26 )
      & ( k4_xboole_0(X26,X27) != X26
        | r1_xboole_0(X26,X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_31,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk3_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk3_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_32,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k7_subset_1(X33,X34,X35) = k4_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))
    & v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))
    & v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))
    & esk5_0 != k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

fof(c_0_34,plain,(
    ! [X40] : k3_yellow_1(X40) = k3_lattice3(k1_lattice3(X40)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

cnf(c_0_35,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k1_enumset1(X4,X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( X1 = X3
    | r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_tarski(X3)))))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X41,X42] :
      ( v2_struct_0(X41)
      | ~ l1_struct_0(X41)
      | v1_xboole_0(X42)
      | ~ v2_waybel_0(X42,k3_yellow_1(k2_struct_0(X41)))
      | ~ v13_waybel_0(X42,k3_yellow_1(k2_struct_0(X41)))
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X41)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X41))),X42,k1_tarski(k1_xboole_0)) = k2_yellow19(X41,k3_yellow19(X41,k2_struct_0(X41),X42)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).

cnf(c_0_43,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( esk1_1(X1) = X2
    | r2_hidden(esk1_1(X1),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2)))))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k1_tarski(X2))))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_27])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) != X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_27])).

cnf(c_0_60,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_27])).

fof(c_0_61,plain,(
    ! [X43,X44,X45] :
      ( v1_xboole_0(X43)
      | v1_xboole_0(X44)
      | ~ v1_subset_1(X44,u1_struct_0(k3_yellow_1(X43)))
      | ~ v2_waybel_0(X44,k3_yellow_1(X43))
      | ~ v13_waybel_0(X44,k3_yellow_1(X43))
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X43))))
      | ~ r2_hidden(X45,X44)
      | ~ v1_xboole_0(X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).

fof(c_0_62,plain,(
    ! [X38] :
      ( ~ l1_struct_0(X38)
      | k2_struct_0(X38) = u1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_63,plain,
    ( esk1_1(X1) = X2
    | v1_xboole_0(X1)
    | ~ r2_hidden(esk1_1(X1),k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_tarski(X1))))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = X1
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_66,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_45]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_45])).

cnf(c_0_68,negated_conjecture,
    ( v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))),esk5_0,X1) = k5_xboole_0(esk5_0,k1_setfam_1(k1_enumset1(esk5_0,esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_73,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_27])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X2,k3_yellow_1(X1))
    | ~ v13_waybel_0(X2,k3_yellow_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_76,plain,(
    ! [X39] :
      ( v2_struct_0(X39)
      | ~ l1_struct_0(X39)
      | ~ v1_xboole_0(u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_77,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( esk1_1(k1_tarski(X1)) = X1
    | v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_37])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(esk5_0,k1_setfam_1(k1_enumset1(esk5_0,esk5_0,k1_tarski(k1_xboole_0)))) = k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),c_0_57])]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_74]),c_0_51])).

cnf(c_0_82,negated_conjecture,
    ( esk5_0 != k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_45]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_84,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk4_0) = k2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_69])).

cnf(c_0_87,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_78]),c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_0,k1_tarski(k1_xboole_0),esk5_0),k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_80]),c_0_82])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,k1_tarski(X1))
    | v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_78])).

cnf(c_0_92,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X3,X2)
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_83,c_0_40])).

cnf(c_0_93,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))) ),
    inference(rw,[status(thm)],[c_0_84,c_0_45])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_xboole_0(k2_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_69])]),c_0_70])).

cnf(c_0_95,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_87,c_0_27])).

cnf(c_0_96,negated_conjecture,
    ( esk2_3(esk5_0,k1_tarski(k1_xboole_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_67]),c_0_93]),c_0_68]),c_0_57])]),c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_80]),c_0_97])]),c_0_82])).

cnf(c_0_100,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.70  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.53/0.70  # and selection function SelectNewComplexAHPNS.
% 0.53/0.70  #
% 0.53/0.70  # Preprocessing time       : 0.028 s
% 0.53/0.70  # Presaturation interreduction done
% 0.53/0.70  
% 0.53/0.70  # Proof found!
% 0.53/0.70  # SZS status Theorem
% 0.53/0.70  # SZS output start CNFRefutation
% 0.53/0.70  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.53/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.53/0.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.53/0.70  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.53/0.70  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.53/0.70  fof(t15_yellow19, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.53/0.70  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.53/0.70  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.53/0.70  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.53/0.70  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.53/0.70  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.53/0.70  fof(t14_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 0.53/0.70  fof(t2_yellow19, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 0.53/0.70  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.53/0.70  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.53/0.70  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.53/0.70  fof(c_0_16, plain, ![X36, X37]:k1_setfam_1(k2_tarski(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.53/0.70  fof(c_0_17, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.53/0.70  fof(c_0_18, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.53/0.70  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.53/0.70  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.53/0.70  fof(c_0_21, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.53/0.70  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.70  cnf(c_0_23, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.53/0.70  fof(c_0_24, plain, ![X30, X31, X32]:(((r2_hidden(X30,X31)|~r2_hidden(X30,k4_xboole_0(X31,k1_tarski(X32))))&(X30!=X32|~r2_hidden(X30,k4_xboole_0(X31,k1_tarski(X32)))))&(~r2_hidden(X30,X31)|X30=X32|r2_hidden(X30,k4_xboole_0(X31,k1_tarski(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.53/0.70  fof(c_0_25, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))))), inference(assume_negation,[status(cth)],[t15_yellow19])).
% 0.53/0.70  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.70  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.53/0.70  cnf(c_0_28, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.53/0.70  fof(c_0_29, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.53/0.70  fof(c_0_30, plain, ![X26, X27]:((~r1_xboole_0(X26,X27)|k4_xboole_0(X26,X27)=X26)&(k4_xboole_0(X26,X27)!=X26|r1_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.53/0.70  fof(c_0_31, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk3_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk3_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.53/0.70  fof(c_0_32, plain, ![X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k7_subset_1(X33,X34,X35)=k4_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.53/0.70  fof(c_0_33, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&(((((~v1_xboole_0(esk5_0)&v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))&v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0))))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))))&esk5_0!=k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).
% 0.53/0.70  fof(c_0_34, plain, ![X40]:k3_yellow_1(X40)=k3_lattice3(k1_lattice3(X40)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.53/0.70  cnf(c_0_35, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k1_enumset1(X4,X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.53/0.70  cnf(c_0_36, plain, (X1=X3|r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_tarski(X3)))))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.53/0.70  cnf(c_0_37, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.70  cnf(c_0_38, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.53/0.70  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.70  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.70  cnf(c_0_41, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.70  fof(c_0_42, plain, ![X41, X42]:(v2_struct_0(X41)|~l1_struct_0(X41)|(v1_xboole_0(X42)|~v2_waybel_0(X42,k3_yellow_1(k2_struct_0(X41)))|~v13_waybel_0(X42,k3_yellow_1(k2_struct_0(X41)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X41)))))|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X41))),X42,k1_tarski(k1_xboole_0))=k2_yellow19(X41,k3_yellow19(X41,k2_struct_0(X41),X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow19])])])])).
% 0.53/0.70  cnf(c_0_43, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.70  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0)))))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_45, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.53/0.70  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.70  cnf(c_0_47, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.70  cnf(c_0_48, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_35])).
% 0.53/0.70  cnf(c_0_49, plain, (esk1_1(X1)=X2|r2_hidden(esk1_1(X1),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2)))))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.53/0.70  cnf(c_0_50, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k1_tarski(X2)))))), inference(rw,[status(thm)],[c_0_38, c_0_27])).
% 0.53/0.70  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_27])).
% 0.53/0.70  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.53/0.70  cnf(c_0_53, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.53/0.70  cnf(c_0_54, negated_conjecture, (v13_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_55, negated_conjecture, (v2_waybel_0(esk5_0,k3_yellow_1(k2_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_56, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_27])).
% 0.53/0.70  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.53/0.70  cnf(c_0_58, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.70  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))!=X1), inference(rw,[status(thm)],[c_0_46, c_0_27])).
% 0.53/0.70  cnf(c_0_60, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_47, c_0_27])).
% 0.53/0.70  fof(c_0_61, plain, ![X43, X44, X45]:(v1_xboole_0(X43)|(v1_xboole_0(X44)|~v1_subset_1(X44,u1_struct_0(k3_yellow_1(X43)))|~v2_waybel_0(X44,k3_yellow_1(X43))|~v13_waybel_0(X44,k3_yellow_1(X43))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X43))))|(~r2_hidden(X45,X44)|~v1_xboole_0(X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_yellow19])])])])).
% 0.53/0.70  fof(c_0_62, plain, ![X38]:(~l1_struct_0(X38)|k2_struct_0(X38)=u1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.53/0.70  cnf(c_0_63, plain, (esk1_1(X1)=X2|v1_xboole_0(X1)|~r2_hidden(esk1_1(X1),k1_tarski(X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.53/0.70  cnf(c_0_64, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,k1_tarski(X1)))))), inference(er,[status(thm)],[c_0_50])).
% 0.53/0.70  cnf(c_0_65, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=X1|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.53/0.70  cnf(c_0_66, plain, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X2,k1_tarski(k1_xboole_0))=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_45]), c_0_45]), c_0_45]), c_0_45])).
% 0.53/0.70  cnf(c_0_67, negated_conjecture, (v13_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_54, c_0_45])).
% 0.53/0.70  cnf(c_0_68, negated_conjecture, (v2_waybel_0(esk5_0,k3_lattice3(k1_lattice3(k2_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_55, c_0_45])).
% 0.53/0.70  cnf(c_0_69, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_70, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_71, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_72, negated_conjecture, (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))),esk5_0,X1)=k5_xboole_0(esk5_0,k1_setfam_1(k1_enumset1(esk5_0,esk5_0,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.53/0.70  cnf(c_0_73, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_58, c_0_27])).
% 0.53/0.70  cnf(c_0_74, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60])])).
% 0.53/0.70  cnf(c_0_75, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))|~v2_waybel_0(X2,k3_yellow_1(X1))|~v13_waybel_0(X2,k3_yellow_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.53/0.70  fof(c_0_76, plain, ![X39]:(v2_struct_0(X39)|~l1_struct_0(X39)|~v1_xboole_0(u1_struct_0(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.53/0.70  cnf(c_0_77, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.53/0.70  cnf(c_0_78, plain, (esk1_1(k1_tarski(X1))=X1|v1_xboole_0(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_63, c_0_37])).
% 0.53/0.70  cnf(c_0_79, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.53/0.70  cnf(c_0_80, negated_conjecture, (k5_xboole_0(esk5_0,k1_setfam_1(k1_enumset1(esk5_0,esk5_0,k1_tarski(k1_xboole_0))))=k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), c_0_57])]), c_0_70]), c_0_71]), c_0_72])).
% 0.53/0.70  cnf(c_0_81, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_74]), c_0_51])).
% 0.53/0.70  cnf(c_0_82, negated_conjecture, (esk5_0!=k2_yellow19(esk4_0,k3_yellow19(esk4_0,k2_struct_0(esk4_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_83, plain, (v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_xboole_0(X3)|~r2_hidden(X3,X2)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_45]), c_0_45]), c_0_45]), c_0_45])).
% 0.53/0.70  cnf(c_0_84, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_85, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.53/0.70  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk4_0)=k2_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_69])).
% 0.53/0.70  cnf(c_0_87, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.70  cnf(c_0_88, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_78]), c_0_79])).
% 0.53/0.70  cnf(c_0_89, negated_conjecture, (r2_hidden(esk2_3(esk5_0,k1_tarski(k1_xboole_0),esk5_0),k1_tarski(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.53/0.70  cnf(c_0_90, negated_conjecture, (~v1_xboole_0(k1_tarski(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_80]), c_0_82])).
% 0.53/0.70  cnf(c_0_91, plain, (r2_hidden(X1,k1_tarski(X1))|v1_xboole_0(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_37, c_0_78])).
% 0.53/0.70  cnf(c_0_92, plain, (v1_xboole_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))|~r2_hidden(X3,X2)|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_83, c_0_40])).
% 0.53/0.70  cnf(c_0_93, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk4_0)))))), inference(rw,[status(thm)],[c_0_84, c_0_45])).
% 0.53/0.70  cnf(c_0_94, negated_conjecture, (~v1_xboole_0(k2_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_69])]), c_0_70])).
% 0.53/0.70  cnf(c_0_95, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_87, c_0_27])).
% 0.53/0.70  cnf(c_0_96, negated_conjecture, (esk2_3(esk5_0,k1_tarski(k1_xboole_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.53/0.70  cnf(c_0_97, negated_conjecture, (r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.53/0.70  cnf(c_0_98, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_67]), c_0_93]), c_0_68]), c_0_57])]), c_0_94])).
% 0.53/0.70  cnf(c_0_99, negated_conjecture, (r2_hidden(k1_xboole_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_80]), c_0_97])]), c_0_82])).
% 0.53/0.70  cnf(c_0_100, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.53/0.70  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])]), ['proof']).
% 0.53/0.70  # SZS output end CNFRefutation
% 0.53/0.70  # Proof object total steps             : 102
% 0.53/0.70  # Proof object clause steps            : 70
% 0.53/0.70  # Proof object formula steps           : 32
% 0.53/0.70  # Proof object conjectures             : 26
% 0.53/0.70  # Proof object clause conjectures      : 23
% 0.53/0.70  # Proof object formula conjectures     : 3
% 0.53/0.70  # Proof object initial clauses used    : 29
% 0.53/0.70  # Proof object initial formulas used   : 16
% 0.53/0.70  # Proof object generating inferences   : 21
% 0.53/0.70  # Proof object simplifying inferences  : 53
% 0.53/0.70  # Training examples: 0 positive, 0 negative
% 0.53/0.70  # Parsed axioms                        : 16
% 0.53/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.70  # Initial clauses                      : 34
% 0.53/0.70  # Removed in clause preprocessing      : 4
% 0.53/0.70  # Initial clauses in saturation        : 30
% 0.53/0.70  # Processed clauses                    : 834
% 0.53/0.70  # ...of these trivial                  : 12
% 0.53/0.70  # ...subsumed                          : 506
% 0.53/0.70  # ...remaining for further processing  : 316
% 0.53/0.70  # Other redundant clauses eliminated   : 67
% 0.53/0.70  # Clauses deleted for lack of memory   : 0
% 0.53/0.70  # Backward-subsumed                    : 6
% 0.53/0.70  # Backward-rewritten                   : 8
% 0.53/0.70  # Generated clauses                    : 14174
% 0.53/0.70  # ...of the previous two non-trivial   : 13868
% 0.53/0.70  # Contextual simplify-reflections      : 5
% 0.53/0.70  # Paramodulations                      : 14078
% 0.53/0.70  # Factorizations                       : 29
% 0.53/0.70  # Equation resolutions                 : 67
% 0.53/0.70  # Propositional unsat checks           : 0
% 0.53/0.70  #    Propositional check models        : 0
% 0.53/0.70  #    Propositional check unsatisfiable : 0
% 0.53/0.70  #    Propositional clauses             : 0
% 0.53/0.70  #    Propositional clauses after purity: 0
% 0.53/0.70  #    Propositional unsat core size     : 0
% 0.53/0.70  #    Propositional preprocessing time  : 0.000
% 0.53/0.70  #    Propositional encoding time       : 0.000
% 0.53/0.70  #    Propositional solver time         : 0.000
% 0.53/0.70  #    Success case prop preproc time    : 0.000
% 0.53/0.70  #    Success case prop encoding time   : 0.000
% 0.53/0.70  #    Success case prop solver time     : 0.000
% 0.53/0.70  # Current number of processed clauses  : 269
% 0.53/0.70  #    Positive orientable unit clauses  : 23
% 0.53/0.70  #    Positive unorientable unit clauses: 0
% 0.53/0.70  #    Negative unit clauses             : 13
% 0.53/0.70  #    Non-unit-clauses                  : 233
% 0.53/0.70  # Current number of unprocessed clauses: 13076
% 0.53/0.70  # ...number of literals in the above   : 78123
% 0.53/0.70  # Current number of archived formulas  : 0
% 0.53/0.70  # Current number of archived clauses   : 47
% 0.53/0.70  # Clause-clause subsumption calls (NU) : 22139
% 0.53/0.70  # Rec. Clause-clause subsumption calls : 7242
% 0.53/0.70  # Non-unit clause-clause subsumptions  : 398
% 0.53/0.70  # Unit Clause-clause subsumption calls : 181
% 0.53/0.70  # Rewrite failures with RHS unbound    : 0
% 0.53/0.70  # BW rewrite match attempts            : 53
% 0.53/0.70  # BW rewrite match successes           : 6
% 0.53/0.70  # Condensation attempts                : 0
% 0.53/0.70  # Condensation successes               : 0
% 0.53/0.70  # Termbank termtop insertions          : 394184
% 0.53/0.71  
% 0.53/0.71  # -------------------------------------------------
% 0.53/0.71  # User time                : 0.352 s
% 0.53/0.71  # System time              : 0.014 s
% 0.53/0.71  # Total time               : 0.366 s
% 0.53/0.71  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

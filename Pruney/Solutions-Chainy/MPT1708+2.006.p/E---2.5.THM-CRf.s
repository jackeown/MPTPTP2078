%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 326 expanded)
%              Number of clauses        :   49 ( 115 expanded)
%              Number of leaves         :   14 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  352 (2630 expanded)
%              Number of equality atoms :   84 ( 405 expanded)
%              Maximal formula depth    :   37 (   5 average)
%              Maximal clause size      :   52 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_pre_topc(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( X4 = k2_tsep_1(X1,X2,X3)
                    <=> u1_struct_0(X4) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(dt_k2_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
        & v1_pre_topc(k2_tsep_1(X1,X2,X3))
        & m1_pre_topc(k2_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(t17_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))
                   => ( ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                          & X5 = X4 )
                      & ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                          & X5 = X4 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_14,plain,(
    ! [X42,X43] : k1_setfam_1(k2_tarski(X42,X43)) = k3_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X51,X52,X53,X54] :
      ( ( X54 != k2_tsep_1(X51,X52,X53)
        | u1_struct_0(X54) = k3_xboole_0(u1_struct_0(X52),u1_struct_0(X53))
        | v2_struct_0(X54)
        | ~ v1_pre_topc(X54)
        | ~ m1_pre_topc(X54,X51)
        | r1_tsep_1(X52,X53)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X51)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X51)
        | v2_struct_0(X51)
        | ~ l1_pre_topc(X51) )
      & ( u1_struct_0(X54) != k3_xboole_0(u1_struct_0(X52),u1_struct_0(X53))
        | X54 = k2_tsep_1(X51,X52,X53)
        | v2_struct_0(X54)
        | ~ v1_pre_topc(X54)
        | ~ m1_pre_topc(X54,X51)
        | r1_tsep_1(X52,X53)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X51)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X51)
        | v2_struct_0(X51)
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X16,X17,X18,X19] : k3_enumset1(X16,X16,X17,X18,X19) = k2_enumset1(X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X20,X21,X22,X23,X24] : k4_enumset1(X20,X20,X21,X22,X23,X24) = k3_enumset1(X20,X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_22,plain,
    ( u1_struct_0(X1) = k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X55,X56,X57] :
      ( ( ~ v2_struct_0(k2_tsep_1(X55,X56,X57))
        | v2_struct_0(X55)
        | ~ l1_pre_topc(X55)
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X56,X55)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X55) )
      & ( v1_pre_topc(k2_tsep_1(X55,X56,X57))
        | v2_struct_0(X55)
        | ~ l1_pre_topc(X55)
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X56,X55)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X55) )
      & ( m1_pre_topc(k2_tsep_1(X55,X56,X57),X55)
        | v2_struct_0(X55)
        | ~ l1_pre_topc(X55)
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X56,X55)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( ~ r1_tsep_1(X2,X3)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))
                     => ( ? [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                            & X5 = X4 )
                        & ? [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                            & X5 = X4 ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_tmap_1])).

cnf(c_0_29,plain,
    ( u1_struct_0(X1) = k1_setfam_1(k4_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_30,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,negated_conjecture,(
    ! [X65,X66] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ r1_tsep_1(esk3_0,esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X65,u1_struct_0(esk3_0))
        | X65 != esk5_0
        | ~ m1_subset_1(X66,u1_struct_0(esk4_0))
        | X66 != esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])])).

cnf(c_0_34,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k1_setfam_1(k4_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | r1_tarski(k1_setfam_1(X45),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_40,negated_conjecture,
    ( k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk4_0))) = u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),c_0_37]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X25
        | X32 = X26
        | X32 = X27
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k4_enumset1(X25,X26,X27,X28,X29,X30) )
      & ( X33 != X25
        | r2_hidden(X33,X31)
        | X31 != k4_enumset1(X25,X26,X27,X28,X29,X30) )
      & ( X33 != X26
        | r2_hidden(X33,X31)
        | X31 != k4_enumset1(X25,X26,X27,X28,X29,X30) )
      & ( X33 != X27
        | r2_hidden(X33,X31)
        | X31 != k4_enumset1(X25,X26,X27,X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k4_enumset1(X25,X26,X27,X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k4_enumset1(X25,X26,X27,X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k4_enumset1(X25,X26,X27,X28,X29,X30) )
      & ( esk1_7(X34,X35,X36,X37,X38,X39,X40) != X34
        | ~ r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k4_enumset1(X34,X35,X36,X37,X38,X39) )
      & ( esk1_7(X34,X35,X36,X37,X38,X39,X40) != X35
        | ~ r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k4_enumset1(X34,X35,X36,X37,X38,X39) )
      & ( esk1_7(X34,X35,X36,X37,X38,X39,X40) != X36
        | ~ r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k4_enumset1(X34,X35,X36,X37,X38,X39) )
      & ( esk1_7(X34,X35,X36,X37,X38,X39,X40) != X37
        | ~ r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k4_enumset1(X34,X35,X36,X37,X38,X39) )
      & ( esk1_7(X34,X35,X36,X37,X38,X39,X40) != X38
        | ~ r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k4_enumset1(X34,X35,X36,X37,X38,X39) )
      & ( esk1_7(X34,X35,X36,X37,X38,X39,X40) != X39
        | ~ r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)
        | X40 = k4_enumset1(X34,X35,X36,X37,X38,X39) )
      & ( r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)
        | esk1_7(X34,X35,X36,X37,X38,X39,X40) = X34
        | esk1_7(X34,X35,X36,X37,X38,X39,X40) = X35
        | esk1_7(X34,X35,X36,X37,X38,X39,X40) = X36
        | esk1_7(X34,X35,X36,X37,X38,X39,X40) = X37
        | esk1_7(X34,X35,X36,X37,X38,X39,X40) = X38
        | esk1_7(X34,X35,X36,X37,X38,X39,X40) = X39
        | X40 = k4_enumset1(X34,X35,X36,X37,X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_45,plain,(
    ! [X9,X10] : r1_tarski(k3_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k1_setfam_1(k4_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0))) = u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_50,plain,(
    ! [X58,X59,X60] :
      ( ( ~ r1_tarski(u1_struct_0(X59),u1_struct_0(X60))
        | m1_pre_topc(X59,X60)
        | ~ m1_pre_topc(X60,X58)
        | ~ m1_pre_topc(X59,X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( ~ m1_pre_topc(X59,X60)
        | r1_tarski(u1_struct_0(X59),u1_struct_0(X60))
        | ~ m1_pre_topc(X60,X58)
        | ~ m1_pre_topc(X59,X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),X1)
    | ~ r2_hidden(X1,k4_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

fof(c_0_54,plain,(
    ! [X48,X49,X50] :
      ( v2_struct_0(X48)
      | ~ l1_pre_topc(X48)
      | v2_struct_0(X49)
      | ~ m1_pre_topc(X49,X48)
      | ~ m1_subset_1(X50,u1_struct_0(X49))
      | m1_subset_1(X50,u1_struct_0(X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_55,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk2_0,X1,esk4_0),esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_36])]),c_0_38]),c_0_37])).

fof(c_0_58,plain,(
    ! [X46,X47] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_pre_topc(X47,X46)
      | l1_pre_topc(X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_62,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_65,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk5_0
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | X2 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(X1))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_35]),c_0_36])])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_35]),c_0_36])])).

cnf(c_0_71,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_63]),c_0_64]),c_0_41]),c_0_36])])).

cnf(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_41]),c_0_36])])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])]),c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_71]),c_0_72])]),c_0_43])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_76]),c_0_35]),c_0_41]),c_0_36])]),c_0_38]),c_0_43]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.029 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.42  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.20/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.42  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.20/0.42  fof(t17_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tmap_1)).
% 0.20/0.42  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.42  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.20/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.42  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.42  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.42  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.42  fof(c_0_14, plain, ![X42, X43]:k1_setfam_1(k2_tarski(X42,X43))=k3_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.42  fof(c_0_15, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.42  fof(c_0_16, plain, ![X51, X52, X53, X54]:((X54!=k2_tsep_1(X51,X52,X53)|u1_struct_0(X54)=k3_xboole_0(u1_struct_0(X52),u1_struct_0(X53))|(v2_struct_0(X54)|~v1_pre_topc(X54)|~m1_pre_topc(X54,X51))|r1_tsep_1(X52,X53)|(v2_struct_0(X53)|~m1_pre_topc(X53,X51))|(v2_struct_0(X52)|~m1_pre_topc(X52,X51))|(v2_struct_0(X51)|~l1_pre_topc(X51)))&(u1_struct_0(X54)!=k3_xboole_0(u1_struct_0(X52),u1_struct_0(X53))|X54=k2_tsep_1(X51,X52,X53)|(v2_struct_0(X54)|~v1_pre_topc(X54)|~m1_pre_topc(X54,X51))|r1_tsep_1(X52,X53)|(v2_struct_0(X53)|~m1_pre_topc(X53,X51))|(v2_struct_0(X52)|~m1_pre_topc(X52,X51))|(v2_struct_0(X51)|~l1_pre_topc(X51)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.20/0.42  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  fof(c_0_19, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.42  fof(c_0_20, plain, ![X16, X17, X18, X19]:k3_enumset1(X16,X16,X17,X18,X19)=k2_enumset1(X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.42  fof(c_0_21, plain, ![X20, X21, X22, X23, X24]:k4_enumset1(X20,X20,X21,X22,X23,X24)=k3_enumset1(X20,X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.42  cnf(c_0_22, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_23, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.42  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_26, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  fof(c_0_27, plain, ![X55, X56, X57]:(((~v2_struct_0(k2_tsep_1(X55,X56,X57))|(v2_struct_0(X55)|~l1_pre_topc(X55)|v2_struct_0(X56)|~m1_pre_topc(X56,X55)|v2_struct_0(X57)|~m1_pre_topc(X57,X55)))&(v1_pre_topc(k2_tsep_1(X55,X56,X57))|(v2_struct_0(X55)|~l1_pre_topc(X55)|v2_struct_0(X56)|~m1_pre_topc(X56,X55)|v2_struct_0(X57)|~m1_pre_topc(X57,X55))))&(m1_pre_topc(k2_tsep_1(X55,X56,X57),X55)|(v2_struct_0(X55)|~l1_pre_topc(X55)|v2_struct_0(X56)|~m1_pre_topc(X56,X55)|v2_struct_0(X57)|~m1_pre_topc(X57,X55)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.20/0.42  fof(c_0_28, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4)))))))), inference(assume_negation,[status(cth)],[t17_tmap_1])).
% 0.20/0.42  cnf(c_0_29, plain, (u1_struct_0(X1)=k1_setfam_1(k4_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tsep_1(X3,X4)|X1!=k2_tsep_1(X2,X3,X4)|~l1_pre_topc(X2)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.42  cnf(c_0_30, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_31, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_32, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  fof(c_0_33, negated_conjecture, ![X65, X66]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(~r1_tsep_1(esk3_0,esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))&(~m1_subset_1(X65,u1_struct_0(esk3_0))|X65!=esk5_0|(~m1_subset_1(X66,u1_struct_0(esk4_0))|X66!=esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])])).
% 0.20/0.42  cnf(c_0_34, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k1_setfam_1(k4_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  fof(c_0_39, plain, ![X44, X45]:(~r2_hidden(X44,X45)|r1_tarski(k1_setfam_1(X45),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk4_0)))=u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))|r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), c_0_37]), c_0_38])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (~r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  fof(c_0_44, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X32,X31)|(X32=X25|X32=X26|X32=X27|X32=X28|X32=X29|X32=X30)|X31!=k4_enumset1(X25,X26,X27,X28,X29,X30))&((((((X33!=X25|r2_hidden(X33,X31)|X31!=k4_enumset1(X25,X26,X27,X28,X29,X30))&(X33!=X26|r2_hidden(X33,X31)|X31!=k4_enumset1(X25,X26,X27,X28,X29,X30)))&(X33!=X27|r2_hidden(X33,X31)|X31!=k4_enumset1(X25,X26,X27,X28,X29,X30)))&(X33!=X28|r2_hidden(X33,X31)|X31!=k4_enumset1(X25,X26,X27,X28,X29,X30)))&(X33!=X29|r2_hidden(X33,X31)|X31!=k4_enumset1(X25,X26,X27,X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k4_enumset1(X25,X26,X27,X28,X29,X30))))&(((((((esk1_7(X34,X35,X36,X37,X38,X39,X40)!=X34|~r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)|X40=k4_enumset1(X34,X35,X36,X37,X38,X39))&(esk1_7(X34,X35,X36,X37,X38,X39,X40)!=X35|~r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)|X40=k4_enumset1(X34,X35,X36,X37,X38,X39)))&(esk1_7(X34,X35,X36,X37,X38,X39,X40)!=X36|~r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)|X40=k4_enumset1(X34,X35,X36,X37,X38,X39)))&(esk1_7(X34,X35,X36,X37,X38,X39,X40)!=X37|~r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)|X40=k4_enumset1(X34,X35,X36,X37,X38,X39)))&(esk1_7(X34,X35,X36,X37,X38,X39,X40)!=X38|~r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)|X40=k4_enumset1(X34,X35,X36,X37,X38,X39)))&(esk1_7(X34,X35,X36,X37,X38,X39,X40)!=X39|~r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)|X40=k4_enumset1(X34,X35,X36,X37,X38,X39)))&(r2_hidden(esk1_7(X34,X35,X36,X37,X38,X39,X40),X40)|(esk1_7(X34,X35,X36,X37,X38,X39,X40)=X34|esk1_7(X34,X35,X36,X37,X38,X39,X40)=X35|esk1_7(X34,X35,X36,X37,X38,X39,X40)=X36|esk1_7(X34,X35,X36,X37,X38,X39,X40)=X37|esk1_7(X34,X35,X36,X37,X38,X39,X40)=X38|esk1_7(X34,X35,X36,X37,X38,X39,X40)=X39)|X40=k4_enumset1(X34,X35,X36,X37,X38,X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.20/0.42  fof(c_0_45, plain, ![X9, X10]:r1_tarski(k3_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.42  cnf(c_0_46, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (k1_setfam_1(k4_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0)))=u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])).
% 0.20/0.42  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.42  cnf(c_0_49, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  fof(c_0_50, plain, ![X58, X59, X60]:((~r1_tarski(u1_struct_0(X59),u1_struct_0(X60))|m1_pre_topc(X59,X60)|~m1_pre_topc(X60,X58)|~m1_pre_topc(X59,X58)|(~v2_pre_topc(X58)|~l1_pre_topc(X58)))&(~m1_pre_topc(X59,X60)|r1_tarski(u1_struct_0(X59),u1_struct_0(X60))|~m1_pre_topc(X60,X58)|~m1_pre_topc(X59,X58)|(~v2_pre_topc(X58)|~l1_pre_topc(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),X1)|~r2_hidden(X1,k4_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.42  cnf(c_0_52, plain, (r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.20/0.42  cnf(c_0_53, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.42  fof(c_0_54, plain, ![X48, X49, X50]:(v2_struct_0(X48)|~l1_pre_topc(X48)|(v2_struct_0(X49)|~m1_pre_topc(X49,X48)|(~m1_subset_1(X50,u1_struct_0(X49))|m1_subset_1(X50,u1_struct_0(X48))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.42  cnf(c_0_55, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk2_0,X1,esk4_0),esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_36])]), c_0_38]), c_0_37])).
% 0.20/0.42  fof(c_0_58, plain, ![X46, X47]:(~l1_pre_topc(X46)|(~m1_pre_topc(X47,X46)|l1_pre_topc(X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_47])).
% 0.20/0.42  cnf(c_0_60, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_41]), c_0_43])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_65, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_55, c_0_59])).
% 0.20/0.42  cnf(c_0_67, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|X1!=esk5_0|~m1_subset_1(X2,u1_struct_0(esk4_0))|X2!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(X1))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_35]), c_0_36])])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_35]), c_0_36])])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_63]), c_0_64]), c_0_41]), c_0_36])])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_41]), c_0_36])])).
% 0.20/0.42  cnf(c_0_73, negated_conjecture, (~m1_subset_1(esk5_0,u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])]), c_0_38])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_71]), c_0_72])]), c_0_43])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_76]), c_0_35]), c_0_41]), c_0_36])]), c_0_38]), c_0_43]), c_0_37]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 78
% 0.20/0.42  # Proof object clause steps            : 49
% 0.20/0.42  # Proof object formula steps           : 29
% 0.20/0.42  # Proof object conjectures             : 32
% 0.20/0.42  # Proof object clause conjectures      : 29
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 25
% 0.20/0.42  # Proof object initial formulas used   : 14
% 0.20/0.42  # Proof object generating inferences   : 18
% 0.20/0.42  # Proof object simplifying inferences  : 54
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 14
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 40
% 0.20/0.42  # Removed in clause preprocessing      : 5
% 0.20/0.42  # Initial clauses in saturation        : 35
% 0.20/0.42  # Processed clauses                    : 299
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 9
% 0.20/0.42  # ...remaining for further processing  : 290
% 0.20/0.42  # Other redundant clauses eliminated   : 46
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 2
% 0.20/0.42  # Backward-rewritten                   : 59
% 0.20/0.42  # Generated clauses                    : 1571
% 0.20/0.42  # ...of the previous two non-trivial   : 1460
% 0.20/0.42  # Contextual simplify-reflections      : 4
% 0.20/0.42  # Paramodulations                      : 1400
% 0.20/0.42  # Factorizations                       : 132
% 0.20/0.42  # Equation resolutions                 : 46
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 185
% 0.20/0.42  #    Positive orientable unit clauses  : 32
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 4
% 0.20/0.42  #    Non-unit-clauses                  : 149
% 0.20/0.42  # Current number of unprocessed clauses: 1231
% 0.20/0.42  # ...number of literals in the above   : 5820
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 101
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 25755
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 11567
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.42  # Unit Clause-clause subsumption calls : 326
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 43
% 0.20/0.42  # BW rewrite match successes           : 3
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 59526
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.070 s
% 0.20/0.42  # System time              : 0.011 s
% 0.20/0.42  # Total time               : 0.081 s
% 0.20/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

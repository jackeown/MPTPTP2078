%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 205 expanded)
%              Number of clauses        :   46 (  98 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  259 ( 949 expanded)
%              Number of equality atoms :   41 ( 163 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   35 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(t29_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(t9_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ~ r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X16)
        | X17 = k4_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X16)
        | r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k4_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X28,X29,X30,X31] :
      ( ( X28 = X30
        | g1_orders_2(X28,X29) != g1_orders_2(X30,X31)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))) )
      & ( X29 = X31
        | g1_orders_2(X28,X29) != g1_orders_2(X30,X31)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)
    | v1_xboole_0(k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_31,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X25] :
      ( ~ l1_orders_2(X25)
      | ~ v1_orders_2(X25)
      | X25 = g1_orders_2(u1_struct_0(X25),u1_orders_2(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_34,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow_6])).

fof(c_0_37,plain,(
    ! [X41,X42,X43] :
      ( ( ~ r1_waybel_0(X41,X42,X43)
        | ~ r2_waybel_0(X41,X42,k6_subset_1(u1_struct_0(X41),X43))
        | v2_struct_0(X42)
        | ~ l1_waybel_0(X42,X41)
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41) )
      & ( r2_waybel_0(X41,X42,k6_subset_1(u1_struct_0(X41),X43))
        | r1_waybel_0(X41,X42,X43)
        | v2_struct_0(X42)
        | ~ l1_waybel_0(X42,X41)
        | v2_struct_0(X41)
        | ~ l1_struct_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).

fof(c_0_38,plain,(
    ! [X21,X22] : k6_subset_1(X21,X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_39,plain,
    ( X1 = X2
    | g1_orders_2(X1,k2_zfmisc_1(X1,X1)) != g1_orders_2(X2,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & v7_waybel_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).

cnf(c_0_43,plain,
    ( r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( X1 = u1_struct_0(X2)
    | g1_orders_2(X1,k2_zfmisc_1(X1,X1)) != X2
    | ~ v1_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_46,plain,(
    ! [X26,X27] :
      ( ( v1_orders_2(g1_orders_2(X26,X27))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) )
      & ( l1_orders_2(g1_orders_2(X26,X27))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_41])).

fof(c_0_48,plain,(
    ! [X33,X34,X35,X36,X38,X40] :
      ( ( m1_subset_1(esk3_4(X33,X34,X35,X36),u1_struct_0(X34))
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ r2_waybel_0(X33,X34,X35)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33) )
      & ( r1_orders_2(X34,X36,esk3_4(X33,X34,X35,X36))
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ r2_waybel_0(X33,X34,X35)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33) )
      & ( r2_hidden(k2_waybel_0(X33,X34,esk3_4(X33,X34,X35,X36)),X35)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ r2_waybel_0(X33,X34,X35)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33) )
      & ( m1_subset_1(esk4_3(X33,X34,X38),u1_struct_0(X34))
        | r2_waybel_0(X33,X34,X38)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X34))
        | ~ r1_orders_2(X34,esk4_3(X33,X34,X38),X40)
        | ~ r2_hidden(k2_waybel_0(X33,X34,X40),X38)
        | r2_waybel_0(X33,X34,X38)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_waybel_0(X1,X2,X3)
    | r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( u1_struct_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1))) = X1
    | ~ v1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))
    | ~ l1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1))) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_41]),c_0_47])).

cnf(c_0_58,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])]),c_0_53]),c_0_54])).

fof(c_0_60,plain,(
    ! [X32] :
      ( ~ l1_orders_2(X32)
      | m1_subset_1(k3_yellow_0(X32),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_61,plain,
    ( u1_struct_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1))) = X1
    | ~ l1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_32])])).

cnf(c_0_62,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,k4_xboole_0(X3,X3))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_41])).

cnf(c_0_65,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( u1_struct_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_32])])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_51]),c_0_52])]),c_0_54]),c_0_53])).

cnf(c_0_68,plain,
    ( m1_subset_1(k3_yellow_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1))),X1)
    | ~ l1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(esk6_0),k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_62]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.028 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.45  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.45  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.20/0.45  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.20/0.45  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.20/0.45  fof(t9_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>~(r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_waybel_0)).
% 0.20/0.45  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.45  fof(dt_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(v1_orders_2(g1_orders_2(X1,X2))&l1_orders_2(g1_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 0.20/0.45  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.20/0.45  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.20/0.45  fof(c_0_12, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:((((r2_hidden(X13,X10)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|X12!=k4_xboole_0(X10,X11)))&(~r2_hidden(X14,X10)|r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k4_xboole_0(X10,X11)))&((~r2_hidden(esk2_3(X15,X16,X17),X17)|(~r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X16))|X17=k4_xboole_0(X15,X16))&((r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))&(~r2_hidden(esk2_3(X15,X16,X17),X16)|r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k4_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.45  fof(c_0_13, plain, ![X19, X20]:(((r1_tarski(X19,X20)|X19!=X20)&(r1_tarski(X20,X19)|X19!=X20))&(~r1_tarski(X19,X20)|~r1_tarski(X20,X19)|X19=X20)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.45  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  fof(c_0_15, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.45  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  fof(c_0_17, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.45  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.45  cnf(c_0_19, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  cnf(c_0_20, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  cnf(c_0_21, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.45  cnf(c_0_22, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.45  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.45  fof(c_0_24, plain, ![X28, X29, X30, X31]:((X28=X30|g1_orders_2(X28,X29)!=g1_orders_2(X30,X31)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))))&(X29=X31|g1_orders_2(X28,X29)!=g1_orders_2(X30,X31)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.20/0.45  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.45  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.45  cnf(c_0_28, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.45  cnf(c_0_29, plain, (v1_xboole_0(k4_xboole_0(X1,X2))|~r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.45  cnf(c_0_30, plain, (r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1)|v1_xboole_0(k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.20/0.45  cnf(c_0_31, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.45  fof(c_0_33, plain, ![X25]:(~l1_orders_2(X25)|(~v1_orders_2(X25)|X25=g1_orders_2(u1_struct_0(X25),u1_orders_2(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.20/0.45  cnf(c_0_34, plain, (X1=k4_xboole_0(X2,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.45  cnf(c_0_35, plain, (v1_xboole_0(k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.45  fof(c_0_36, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.20/0.45  fof(c_0_37, plain, ![X41, X42, X43]:((~r1_waybel_0(X41,X42,X43)|~r2_waybel_0(X41,X42,k6_subset_1(u1_struct_0(X41),X43))|(v2_struct_0(X42)|~l1_waybel_0(X42,X41))|(v2_struct_0(X41)|~l1_struct_0(X41)))&(r2_waybel_0(X41,X42,k6_subset_1(u1_struct_0(X41),X43))|r1_waybel_0(X41,X42,X43)|(v2_struct_0(X42)|~l1_waybel_0(X42,X41))|(v2_struct_0(X41)|~l1_struct_0(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_waybel_0])])])])])).
% 0.20/0.45  fof(c_0_38, plain, ![X21, X22]:k6_subset_1(X21,X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.45  cnf(c_0_39, plain, (X1=X2|g1_orders_2(X1,k2_zfmisc_1(X1,X1))!=g1_orders_2(X2,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.45  cnf(c_0_40, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_41, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.45  fof(c_0_42, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk5_0))&~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).
% 0.20/0.45  cnf(c_0_43, plain, (r2_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.45  cnf(c_0_44, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.45  cnf(c_0_45, plain, (X1=u1_struct_0(X2)|g1_orders_2(X1,k2_zfmisc_1(X1,X1))!=X2|~v1_orders_2(X2)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.45  fof(c_0_46, plain, ![X26, X27]:((v1_orders_2(g1_orders_2(X26,X27))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))))&(l1_orders_2(g1_orders_2(X26,X27))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).
% 0.20/0.45  cnf(c_0_47, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_21, c_0_41])).
% 0.20/0.45  fof(c_0_48, plain, ![X33, X34, X35, X36, X38, X40]:((((m1_subset_1(esk3_4(X33,X34,X35,X36),u1_struct_0(X34))|~m1_subset_1(X36,u1_struct_0(X34))|~r2_waybel_0(X33,X34,X35)|(v2_struct_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~l1_struct_0(X33)))&(r1_orders_2(X34,X36,esk3_4(X33,X34,X35,X36))|~m1_subset_1(X36,u1_struct_0(X34))|~r2_waybel_0(X33,X34,X35)|(v2_struct_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~l1_struct_0(X33))))&(r2_hidden(k2_waybel_0(X33,X34,esk3_4(X33,X34,X35,X36)),X35)|~m1_subset_1(X36,u1_struct_0(X34))|~r2_waybel_0(X33,X34,X35)|(v2_struct_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~l1_struct_0(X33))))&((m1_subset_1(esk4_3(X33,X34,X38),u1_struct_0(X34))|r2_waybel_0(X33,X34,X38)|(v2_struct_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~l1_struct_0(X33)))&(~m1_subset_1(X40,u1_struct_0(X34))|~r1_orders_2(X34,esk4_3(X33,X34,X38),X40)|~r2_hidden(k2_waybel_0(X33,X34,X40),X38)|r2_waybel_0(X33,X34,X38)|(v2_struct_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~l1_struct_0(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.20/0.45  cnf(c_0_49, negated_conjecture, (~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_50, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r1_waybel_0(X1,X2,X3)|r2_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.45  cnf(c_0_51, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_52, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_55, plain, (u1_struct_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))=X1|~v1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))|~l1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.45  cnf(c_0_56, plain, (v1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.45  cnf(c_0_57, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_41]), c_0_47])).
% 0.20/0.45  cnf(c_0_58, plain, (r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])]), c_0_53]), c_0_54])).
% 0.20/0.45  fof(c_0_60, plain, ![X32]:(~l1_orders_2(X32)|m1_subset_1(k3_yellow_0(X32),u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.20/0.45  cnf(c_0_61, plain, (u1_struct_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))=X1|~l1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_32])])).
% 0.20/0.45  cnf(c_0_62, plain, (l1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.45  cnf(c_0_63, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X1,X2,k4_xboole_0(X3,X3))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.45  cnf(c_0_64, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_59, c_0_41])).
% 0.20/0.45  cnf(c_0_65, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.45  cnf(c_0_66, plain, (u1_struct_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_32])])).
% 0.20/0.45  cnf(c_0_67, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_51]), c_0_52])]), c_0_54]), c_0_53])).
% 0.20/0.45  cnf(c_0_68, plain, (m1_subset_1(k3_yellow_0(g1_orders_2(X1,k2_zfmisc_1(X1,X1))),X1)|~l1_orders_2(g1_orders_2(X1,k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.45  cnf(c_0_69, negated_conjecture, (~l1_orders_2(g1_orders_2(u1_struct_0(esk6_0),k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk6_0))))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.45  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_62]), c_0_32])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 71
% 0.20/0.45  # Proof object clause steps            : 46
% 0.20/0.45  # Proof object formula steps           : 25
% 0.20/0.45  # Proof object conjectures             : 13
% 0.20/0.45  # Proof object clause conjectures      : 10
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 21
% 0.20/0.45  # Proof object initial formulas used   : 12
% 0.20/0.45  # Proof object generating inferences   : 23
% 0.20/0.45  # Proof object simplifying inferences  : 19
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 12
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 34
% 0.20/0.45  # Removed in clause preprocessing      : 1
% 0.20/0.45  # Initial clauses in saturation        : 33
% 0.20/0.45  # Processed clauses                    : 1493
% 0.20/0.45  # ...of these trivial                  : 22
% 0.20/0.45  # ...subsumed                          : 1224
% 0.20/0.45  # ...remaining for further processing  : 247
% 0.20/0.45  # Other redundant clauses eliminated   : 22
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 6
% 0.20/0.45  # Backward-rewritten                   : 7
% 0.20/0.45  # Generated clauses                    : 4651
% 0.20/0.45  # ...of the previous two non-trivial   : 3955
% 0.20/0.45  # Contextual simplify-reflections      : 5
% 0.20/0.45  # Paramodulations                      : 4601
% 0.20/0.45  # Factorizations                       : 12
% 0.20/0.45  # Equation resolutions                 : 38
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 200
% 0.20/0.45  #    Positive orientable unit clauses  : 23
% 0.20/0.45  #    Positive unorientable unit clauses: 3
% 0.20/0.45  #    Negative unit clauses             : 10
% 0.20/0.45  #    Non-unit-clauses                  : 164
% 0.20/0.45  # Current number of unprocessed clauses: 2511
% 0.20/0.45  # ...number of literals in the above   : 7705
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 46
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 14737
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 7824
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 758
% 0.20/0.45  # Unit Clause-clause subsumption calls : 687
% 0.20/0.45  # Rewrite failures with RHS unbound    : 125
% 0.20/0.45  # BW rewrite match attempts            : 214
% 0.20/0.45  # BW rewrite match successes           : 28
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 53817
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.102 s
% 0.20/0.45  # System time              : 0.010 s
% 0.20/0.45  # Total time               : 0.112 s
% 0.20/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

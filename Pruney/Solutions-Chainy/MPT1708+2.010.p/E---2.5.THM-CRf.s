%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 459 expanded)
%              Number of clauses        :   44 ( 166 expanded)
%              Number of leaves         :   10 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  296 (4215 expanded)
%              Number of equality atoms :   39 ( 541 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_10,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X28 != k2_tsep_1(X25,X26,X27)
        | u1_struct_0(X28) = k3_xboole_0(u1_struct_0(X26),u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X25)
        | r1_tsep_1(X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) )
      & ( u1_struct_0(X28) != k3_xboole_0(u1_struct_0(X26),u1_struct_0(X27))
        | X28 = k2_tsep_1(X25,X26,X27)
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X25)
        | r1_tsep_1(X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

fof(c_0_11,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_12,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v2_struct_0(k2_tsep_1(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29) )
      & ( v1_pre_topc(k2_tsep_1(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29) )
      & ( m1_pre_topc(k2_tsep_1(X29,X30,X31),X29)
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_15,negated_conjecture,(
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

cnf(c_0_16,plain,
    ( u1_struct_0(X1) = k4_xboole_0(u1_struct_0(X3),k4_xboole_0(u1_struct_0(X3),u1_struct_0(X4)))
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
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,negated_conjecture,(
    ! [X36,X37] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ r1_tsep_1(esk3_0,esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X36,u1_struct_0(esk3_0))
        | X36 != esk5_0
        | ~ m1_subset_1(X37,u1_struct_0(esk4_0))
        | X37 != esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_21,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_22,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k4_xboole_0(u1_struct_0(X2),k4_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)))
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_34,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) = k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk5_0
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | X2 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    | r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( X1 != esk5_0
    | X2 != esk5_0
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    | ~ r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    | r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

fof(c_0_49,plain,(
    ! [X24] :
      ( v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | ~ v1_xboole_0(u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_50,negated_conjecture,
    ( X1 != esk5_0
    | X2 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    | r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    | X1 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

fof(c_0_56,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_57,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | l1_pre_topc(k2_tsep_1(X1,X2,X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_23]),c_0_32]),c_0_24])]),c_0_25]),c_0_33]),c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_63]),c_0_23]),c_0_32]),c_0_24])]),c_0_26]),c_0_33]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.21/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.028 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.21/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.38  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.21/0.38  fof(t17_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tmap_1)).
% 0.21/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.21/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.21/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.38  fof(c_0_10, plain, ![X25, X26, X27, X28]:((X28!=k2_tsep_1(X25,X26,X27)|u1_struct_0(X28)=k3_xboole_0(u1_struct_0(X26),u1_struct_0(X27))|(v2_struct_0(X28)|~v1_pre_topc(X28)|~m1_pre_topc(X28,X25))|r1_tsep_1(X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~l1_pre_topc(X25)))&(u1_struct_0(X28)!=k3_xboole_0(u1_struct_0(X26),u1_struct_0(X27))|X28=k2_tsep_1(X25,X26,X27)|(v2_struct_0(X28)|~v1_pre_topc(X28)|~m1_pre_topc(X28,X25))|r1_tsep_1(X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.21/0.38  fof(c_0_11, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.38  cnf(c_0_12, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  fof(c_0_14, plain, ![X29, X30, X31]:(((~v2_struct_0(k2_tsep_1(X29,X30,X31))|(v2_struct_0(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~m1_pre_topc(X30,X29)|v2_struct_0(X31)|~m1_pre_topc(X31,X29)))&(v1_pre_topc(k2_tsep_1(X29,X30,X31))|(v2_struct_0(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~m1_pre_topc(X30,X29)|v2_struct_0(X31)|~m1_pre_topc(X31,X29))))&(m1_pre_topc(k2_tsep_1(X29,X30,X31),X29)|(v2_struct_0(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~m1_pre_topc(X30,X29)|v2_struct_0(X31)|~m1_pre_topc(X31,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.21/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4)))))))), inference(assume_negation,[status(cth)],[t17_tmap_1])).
% 0.21/0.38  cnf(c_0_16, plain, (u1_struct_0(X1)=k4_xboole_0(u1_struct_0(X3),k4_xboole_0(u1_struct_0(X3),u1_struct_0(X4)))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tsep_1(X3,X4)|X1!=k2_tsep_1(X2,X3,X4)|~l1_pre_topc(X2)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.38  cnf(c_0_17, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_18, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  fof(c_0_20, negated_conjecture, ![X36, X37]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(~r1_tsep_1(esk3_0,esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))&(~m1_subset_1(X36,u1_struct_0(esk3_0))|X36!=esk5_0|(~m1_subset_1(X37,u1_struct_0(esk4_0))|X37!=esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).
% 0.21/0.38  fof(c_0_21, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.38  cnf(c_0_22, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k4_xboole_0(u1_struct_0(X2),k4_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))|r1_tsep_1(X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_17]), c_0_18]), c_0_19])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  fof(c_0_27, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.21/0.38  cnf(c_0_28, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (~r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))=k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)))|r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25]), c_0_26])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  fof(c_0_34, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.21/0.38  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (v1_xboole_0(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))|r2_hidden(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))=k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.21/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|X1!=esk5_0|~m1_subset_1(X2,u1_struct_0(esk4_0))|X2!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.38  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_35])).
% 0.21/0.38  cnf(c_0_42, negated_conjecture, (v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))|r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 0.21/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_38])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (X1!=esk5_0|X2!=esk5_0|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.38  cnf(c_0_46, negated_conjecture, (v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))|~r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.38  cnf(c_0_47, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_43])).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))|r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.21/0.38  fof(c_0_49, plain, ![X24]:(v2_struct_0(X24)|~l1_struct_0(X24)|~v1_xboole_0(u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (X1!=esk5_0|X2!=esk5_0|~r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.21/0.38  cnf(c_0_51, negated_conjecture, (v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))|r2_hidden(esk5_0,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.21/0.38  cnf(c_0_52, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))|X1!=esk5_0|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.38  cnf(c_0_54, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|~v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_52, c_0_37])).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.21/0.38  fof(c_0_56, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.38  fof(c_0_57, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.38  cnf(c_0_58, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.21/0.38  cnf(c_0_59, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.38  cnf(c_0_60, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.38  cnf(c_0_61, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.38  cnf(c_0_62, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|l1_pre_topc(k2_tsep_1(X1,X2,X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_60, c_0_17])).
% 0.21/0.38  cnf(c_0_63, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_23]), c_0_32]), c_0_24])]), c_0_25]), c_0_33]), c_0_26])).
% 0.21/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_63]), c_0_23]), c_0_32]), c_0_24])]), c_0_26]), c_0_33]), c_0_25]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 65
% 0.21/0.38  # Proof object clause steps            : 44
% 0.21/0.38  # Proof object formula steps           : 21
% 0.21/0.38  # Proof object conjectures             : 28
% 0.21/0.38  # Proof object clause conjectures      : 25
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 22
% 0.21/0.38  # Proof object initial formulas used   : 10
% 0.21/0.38  # Proof object generating inferences   : 19
% 0.21/0.38  # Proof object simplifying inferences  : 30
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 10
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 27
% 0.21/0.38  # Removed in clause preprocessing      : 1
% 0.21/0.38  # Initial clauses in saturation        : 26
% 0.21/0.38  # Processed clauses                    : 107
% 0.21/0.38  # ...of these trivial                  : 1
% 0.21/0.38  # ...subsumed                          : 12
% 0.21/0.38  # ...remaining for further processing  : 94
% 0.21/0.38  # Other redundant clauses eliminated   : 3
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 10
% 0.21/0.38  # Generated clauses                    : 123
% 0.21/0.38  # ...of the previous two non-trivial   : 104
% 0.21/0.38  # Contextual simplify-reflections      : 5
% 0.21/0.38  # Paramodulations                      : 114
% 0.21/0.38  # Factorizations                       : 2
% 0.21/0.38  # Equation resolutions                 : 7
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 58
% 0.21/0.38  #    Positive orientable unit clauses  : 12
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 4
% 0.21/0.38  #    Non-unit-clauses                  : 42
% 0.21/0.38  # Current number of unprocessed clauses: 49
% 0.21/0.38  # ...number of literals in the above   : 192
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 37
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 1003
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 267
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 17
% 0.21/0.38  # Unit Clause-clause subsumption calls : 52
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 10
% 0.21/0.38  # BW rewrite match successes           : 3
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 4475
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.035 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.040 s
% 0.21/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

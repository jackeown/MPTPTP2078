%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 736 expanded)
%              Number of clauses        :   47 ( 259 expanded)
%              Number of leaves         :    9 ( 184 expanded)
%              Depth                    :   16
%              Number of atoms          :  310 (6699 expanded)
%              Number of equality atoms :   39 ( 837 expanded)
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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_9,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X26 != k2_tsep_1(X23,X24,X25)
        | u1_struct_0(X26) = k3_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X23)
        | r1_tsep_1(X24,X25)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) )
      & ( u1_struct_0(X26) != k3_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | X26 = k2_tsep_1(X23,X24,X25)
        | v2_struct_0(X26)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X23)
        | r1_tsep_1(X24,X25)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

fof(c_0_10,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_11,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v2_struct_0(k2_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( v1_pre_topc(k2_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( m1_pre_topc(k2_tsep_1(X27,X28,X29),X27)
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_14,negated_conjecture,(
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

cnf(c_0_15,plain,
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
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,(
    ! [X34,X35] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ r1_tsep_1(esk3_0,esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X34,u1_struct_0(esk3_0))
        | X34 != esk5_0
        | ~ m1_subset_1(X35,u1_struct_0(esk4_0))
        | X35 != esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_20,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ v1_xboole_0(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_21,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_22,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k4_xboole_0(u1_struct_0(X2),k4_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)))
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_33,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | l1_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) = k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_36,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X18,X17)
        | r2_hidden(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ r2_hidden(X18,X17)
        | m1_subset_1(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X18,X17)
        | v1_xboole_0(X18)
        | ~ v1_xboole_0(X17) )
      & ( ~ v1_xboole_0(X18)
        | m1_subset_1(X18,X17)
        | ~ v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ l1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | l1_pre_topc(k2_tsep_1(X1,X2,X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_16])).

fof(c_0_40,plain,(
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

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_23]),c_0_31]),c_0_24])]),c_0_25]),c_0_32]),c_0_26])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_43]),c_0_23]),c_0_31]),c_0_24])]),c_0_26]),c_0_32]),c_0_25])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk5_0
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | X2 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_35]),c_0_35]),c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | X1 != esk5_0
    | X2 != esk5_0
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | X1 != esk5_0
    | X2 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X2,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | X1 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_24])])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_61]),c_0_62])]),c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_24])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_63]),c_0_64])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.047 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.19/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.40  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.19/0.40  fof(t17_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tmap_1)).
% 0.19/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.40  fof(c_0_9, plain, ![X23, X24, X25, X26]:((X26!=k2_tsep_1(X23,X24,X25)|u1_struct_0(X26)=k3_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|(v2_struct_0(X26)|~v1_pre_topc(X26)|~m1_pre_topc(X26,X23))|r1_tsep_1(X24,X25)|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(v2_struct_0(X24)|~m1_pre_topc(X24,X23))|(v2_struct_0(X23)|~l1_pre_topc(X23)))&(u1_struct_0(X26)!=k3_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|X26=k2_tsep_1(X23,X24,X25)|(v2_struct_0(X26)|~v1_pre_topc(X26)|~m1_pre_topc(X26,X23))|r1_tsep_1(X24,X25)|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(v2_struct_0(X24)|~m1_pre_topc(X24,X23))|(v2_struct_0(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.19/0.40  fof(c_0_10, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.40  cnf(c_0_11, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_13, plain, ![X27, X28, X29]:(((~v2_struct_0(k2_tsep_1(X27,X28,X29))|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27)))&(v1_pre_topc(k2_tsep_1(X27,X28,X29))|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27))))&(m1_pre_topc(k2_tsep_1(X27,X28,X29),X27)|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.19/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4)))))))), inference(assume_negation,[status(cth)],[t17_tmap_1])).
% 0.19/0.40  cnf(c_0_15, plain, (u1_struct_0(X1)=k4_xboole_0(u1_struct_0(X3),k4_xboole_0(u1_struct_0(X3),u1_struct_0(X4)))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tsep_1(X3,X4)|X1!=k2_tsep_1(X2,X3,X4)|~l1_pre_topc(X2)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.40  cnf(c_0_16, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_17, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  fof(c_0_19, negated_conjecture, ![X34, X35]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(~r1_tsep_1(esk3_0,esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))&(~m1_subset_1(X34,u1_struct_0(esk3_0))|X34!=esk5_0|(~m1_subset_1(X35,u1_struct_0(esk4_0))|X35!=esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.19/0.40  fof(c_0_20, plain, ![X22]:(v2_struct_0(X22)|~l1_struct_0(X22)|~v1_xboole_0(u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.40  fof(c_0_21, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.40  cnf(c_0_22, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k4_xboole_0(u1_struct_0(X2),k4_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))|r1_tsep_1(X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_27, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (~r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))=k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)))|r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25]), c_0_26])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  fof(c_0_33, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|l1_pre_topc(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.40  cnf(c_0_34, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))=k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])]), c_0_32])).
% 0.19/0.40  cnf(c_0_36, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  fof(c_0_37, plain, ![X17, X18]:(((~m1_subset_1(X18,X17)|r2_hidden(X18,X17)|v1_xboole_0(X17))&(~r2_hidden(X18,X17)|m1_subset_1(X18,X17)|v1_xboole_0(X17)))&((~m1_subset_1(X18,X17)|v1_xboole_0(X18)|~v1_xboole_0(X17))&(~v1_xboole_0(X18)|m1_subset_1(X18,X17)|~v1_xboole_0(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|~l1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0))|~v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.40  cnf(c_0_39, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|l1_pre_topc(k2_tsep_1(X1,X2,X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_16])).
% 0.19/0.40  fof(c_0_40, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.40  cnf(c_0_41, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|~v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_23]), c_0_31]), c_0_24])]), c_0_25]), c_0_32]), c_0_26])).
% 0.19/0.40  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (v1_xboole_0(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))|r2_hidden(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_43]), c_0_23]), c_0_31]), c_0_24])]), c_0_26]), c_0_32]), c_0_25])).
% 0.19/0.40  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|X1!=esk5_0|~m1_subset_1(X2,u1_struct_0(esk4_0))|X2!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_50, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_35]), c_0_35]), c_0_46])).
% 0.19/0.40  cnf(c_0_52, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|X1!=esk5_0|X2!=esk5_0|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (~r2_hidden(esk5_0,k4_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.40  cnf(c_0_56, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|X1!=esk5_0|X2!=esk5_0|~r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X2,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_49])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|X1!=esk5_0|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_57])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_24])])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_61]), c_0_62])]), c_0_26])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_24])])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_63]), c_0_64])]), c_0_32]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 66
% 0.19/0.40  # Proof object clause steps            : 47
% 0.19/0.40  # Proof object formula steps           : 19
% 0.19/0.40  # Proof object conjectures             : 30
% 0.19/0.40  # Proof object clause conjectures      : 27
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 22
% 0.19/0.40  # Proof object initial formulas used   : 9
% 0.19/0.40  # Proof object generating inferences   : 23
% 0.19/0.40  # Proof object simplifying inferences  : 40
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 9
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 29
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 28
% 0.19/0.40  # Processed clauses                    : 124
% 0.19/0.40  # ...of these trivial                  : 1
% 0.19/0.40  # ...subsumed                          : 12
% 0.19/0.40  # ...remaining for further processing  : 111
% 0.19/0.40  # Other redundant clauses eliminated   : 3
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 16
% 0.19/0.40  # Backward-rewritten                   : 9
% 0.19/0.40  # Generated clauses                    : 133
% 0.19/0.40  # ...of the previous two non-trivial   : 113
% 0.19/0.40  # Contextual simplify-reflections      : 4
% 0.19/0.40  # Paramodulations                      : 124
% 0.19/0.40  # Factorizations                       : 2
% 0.19/0.40  # Equation resolutions                 : 7
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 58
% 0.19/0.40  #    Positive orientable unit clauses  : 14
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 6
% 0.19/0.40  #    Non-unit-clauses                  : 38
% 0.19/0.40  # Current number of unprocessed clauses: 42
% 0.19/0.40  # ...number of literals in the above   : 191
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 54
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1334
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 163
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 31
% 0.19/0.40  # Unit Clause-clause subsumption calls : 65
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 6
% 0.19/0.40  # BW rewrite match successes           : 2
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 4995
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.061 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.066 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

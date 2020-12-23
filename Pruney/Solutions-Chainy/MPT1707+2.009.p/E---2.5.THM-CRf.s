%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:51 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 135 expanded)
%              Number of clauses        :   34 (  50 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  263 (1149 expanded)
%              Number of equality atoms :   27 ( 132 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_tmap_1,conjecture,(
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
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                 => ~ ( ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => X5 != X4 )
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => X5 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d2_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_pre_topc(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( X4 = k1_tsep_1(X1,X2,X3)
                  <=> u1_struct_0(X4) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_9,negated_conjecture,(
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
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                   => ~ ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => X5 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => X5 != X4 ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tmap_1])).

fof(c_0_10,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_11,negated_conjecture,(
    ! [X34,X35] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X34,u1_struct_0(esk3_0))
        | X34 != esk5_0 )
      & ( ~ m1_subset_1(X35,u1_struct_0(esk4_0))
        | X35 != esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X26 != k1_tsep_1(X23,X24,X25)
        | u1_struct_0(X26) = k2_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) )
      & ( u1_struct_0(X26) != k2_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | X26 = k1_tsep_1(X23,X24,X25)
        | v2_struct_0(X26)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v2_struct_0(k1_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( v1_pre_topc(k1_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( m1_pre_topc(k1_tsep_1(X27,X28,X29),X27)
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( u1_struct_0(X1) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k1_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | X1 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))
    | r2_hidden(esk5_0,k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_29]),c_0_30])).

fof(c_0_35,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ v1_xboole_0(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( X1 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( X1 != esk5_0
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))
    | r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_struct_0(k1_tsep_1(X3,X2,X1))
    | ~ l1_pre_topc(X3)
    | ~ v1_xboole_0(k2_xboole_0(u1_struct_0(X2),u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_44,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_45,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | l1_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_46,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_30]),c_0_29])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(k1_tsep_1(X1,esk3_0,esk4_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | l1_pre_topc(k1_tsep_1(X1,X2,X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_29]),c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_25]),c_0_26]),c_0_27])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t16_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>~((![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>X5!=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X3))=>X5!=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tmap_1)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.20/0.39  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.20/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>~((![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>X5!=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X3))=>X5!=X4)))))))), inference(assume_negation,[status(cth)],[t16_tmap_1])).
% 0.20/0.39  fof(c_0_10, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, ![X34, X35]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))&((~m1_subset_1(X34,u1_struct_0(esk3_0))|X34!=esk5_0)&(~m1_subset_1(X35,u1_struct_0(esk4_0))|X35!=esk5_0)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.20/0.39  fof(c_0_12, plain, ![X23, X24, X25, X26]:((X26!=k1_tsep_1(X23,X24,X25)|u1_struct_0(X26)=k2_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|(v2_struct_0(X26)|~v1_pre_topc(X26)|~m1_pre_topc(X26,X23))|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(v2_struct_0(X24)|~m1_pre_topc(X24,X23))|(v2_struct_0(X23)|~l1_pre_topc(X23)))&(u1_struct_0(X26)!=k2_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|X26=k1_tsep_1(X23,X24,X25)|(v2_struct_0(X26)|~v1_pre_topc(X26)|~m1_pre_topc(X26,X23))|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(v2_struct_0(X24)|~m1_pre_topc(X24,X23))|(v2_struct_0(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.20/0.39  fof(c_0_13, plain, ![X27, X28, X29]:(((~v2_struct_0(k1_tsep_1(X27,X28,X29))|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27)))&(v1_pre_topc(k1_tsep_1(X27,X28,X29))|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27))))&(m1_pre_topc(k1_tsep_1(X27,X28,X29),X27)|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(r2_hidden(X9,X6)|r2_hidden(X9,X7))|X8!=k2_xboole_0(X6,X7))&((~r2_hidden(X10,X6)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))&(~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))))&(((~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k2_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.39  cnf(c_0_15, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_17, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_19, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_20, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  fof(c_0_21, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))|r2_hidden(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.39  cnf(c_0_24, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk4_0))|X1!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_33, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))|r2_hidden(esk5_0,k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_29]), c_0_30])).
% 0.20/0.39  fof(c_0_35, plain, ![X22]:(v2_struct_0(X22)|~l1_struct_0(X22)|~v1_xboole_0(u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|X1!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (X1!=esk5_0|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))|r2_hidden(esk5_0,u1_struct_0(esk4_0))|r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_39, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (X1!=esk5_0|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))|r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.39  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_struct_0(k1_tsep_1(X3,X2,X1))|~l1_pre_topc(X3)|~v1_xboole_0(k2_xboole_0(u1_struct_0(X2),u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_24]), c_0_20])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.39  fof(c_0_44, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  fof(c_0_45, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|l1_pre_topc(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0))|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_30]), c_0_29])).
% 0.20/0.39  cnf(c_0_47, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_48, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(k1_tsep_1(X1,esk3_0,esk4_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|l1_pre_topc(k1_tsep_1(X1,X2,X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_48, c_0_18])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_29]), c_0_30])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_25]), c_0_26]), c_0_27])]), c_0_28]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 53
% 0.20/0.39  # Proof object clause steps            : 34
% 0.20/0.39  # Proof object formula steps           : 19
% 0.20/0.39  # Proof object conjectures             : 23
% 0.20/0.39  # Proof object clause conjectures      : 20
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 19
% 0.20/0.39  # Proof object initial formulas used   : 9
% 0.20/0.39  # Proof object generating inferences   : 15
% 0.20/0.39  # Proof object simplifying inferences  : 19
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 9
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 26
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 26
% 0.20/0.39  # Processed clauses                    : 185
% 0.20/0.39  # ...of these trivial                  : 10
% 0.20/0.39  # ...subsumed                          : 44
% 0.20/0.39  # ...remaining for further processing  : 131
% 0.20/0.39  # Other redundant clauses eliminated   : 3
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 13
% 0.20/0.39  # Backward-rewritten                   : 5
% 0.20/0.39  # Generated clauses                    : 448
% 0.20/0.39  # ...of the previous two non-trivial   : 371
% 0.20/0.39  # Contextual simplify-reflections      : 7
% 0.20/0.39  # Paramodulations                      : 393
% 0.20/0.39  # Factorizations                       : 48
% 0.20/0.39  # Equation resolutions                 : 7
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 87
% 0.20/0.39  #    Positive orientable unit clauses  : 14
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 70
% 0.20/0.39  # Current number of unprocessed clauses: 237
% 0.20/0.39  # ...number of literals in the above   : 1034
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 44
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 3128
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 594
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 64
% 0.20/0.39  # Unit Clause-clause subsumption calls : 85
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 24
% 0.20/0.39  # BW rewrite match successes           : 4
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9728
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.042 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.047 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

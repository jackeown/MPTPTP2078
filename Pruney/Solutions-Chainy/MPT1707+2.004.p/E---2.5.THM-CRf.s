%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 223 expanded)
%              Number of clauses        :   40 (  87 expanded)
%              Number of leaves         :    6 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  255 (1810 expanded)
%              Number of equality atoms :   29 ( 217 expanded)
%              Maximal formula depth    :   17 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X32,X33] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk3_0)
      & m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))
      & ( ~ m1_subset_1(X32,u1_struct_0(esk4_0))
        | X32 != esk6_0 )
      & ( ~ m1_subset_1(X33,u1_struct_0(esk5_0))
        | X33 != esk6_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X21,X22,X23,X24] :
      ( ( X24 != k1_tsep_1(X21,X22,X23)
        | u1_struct_0(X24) = k2_xboole_0(u1_struct_0(X22),u1_struct_0(X23))
        | v2_struct_0(X24)
        | ~ v1_pre_topc(X24)
        | ~ m1_pre_topc(X24,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) )
      & ( u1_struct_0(X24) != k2_xboole_0(u1_struct_0(X22),u1_struct_0(X23))
        | X24 = k1_tsep_1(X21,X22,X23)
        | v2_struct_0(X24)
        | ~ v1_pre_topc(X24)
        | ~ m1_pre_topc(X24,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_10,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_struct_0(k1_tsep_1(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) )
      & ( v1_pre_topc(k1_tsep_1(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) )
      & ( m1_pre_topc(k1_tsep_1(X25,X26,X27),X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X16)
        | ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X17)
        | r2_hidden(esk2_3(X15,X16,X17),X15)
        | r2_hidden(esk2_3(X15,X16,X17),X16)
        | X17 = k2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))
    | v1_xboole_0(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | X1 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk6_0,k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | X1 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( X1 != esk6_0
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0))
    | r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( X1 != esk6_0
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( X1 != esk6_0
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.043 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t16_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>~((![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>X5!=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X3))=>X5!=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tmap_1)).
% 0.13/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.39  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.13/0.39  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.13/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.13/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>~((![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>X5!=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X3))=>X5!=X4)))))))), inference(assume_negation,[status(cth)],[t16_tmap_1])).
% 0.13/0.39  fof(c_0_7, plain, ![X19, X20]:(((~m1_subset_1(X20,X19)|r2_hidden(X20,X19)|v1_xboole_0(X19))&(~r2_hidden(X20,X19)|m1_subset_1(X20,X19)|v1_xboole_0(X19)))&((~m1_subset_1(X20,X19)|v1_xboole_0(X20)|~v1_xboole_0(X19))&(~v1_xboole_0(X20)|m1_subset_1(X20,X19)|~v1_xboole_0(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.39  fof(c_0_8, negated_conjecture, ![X32, X33]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))&((~m1_subset_1(X32,u1_struct_0(esk4_0))|X32!=esk6_0)&(~m1_subset_1(X33,u1_struct_0(esk5_0))|X33!=esk6_0)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).
% 0.13/0.39  fof(c_0_9, plain, ![X21, X22, X23, X24]:((X24!=k1_tsep_1(X21,X22,X23)|u1_struct_0(X24)=k2_xboole_0(u1_struct_0(X22),u1_struct_0(X23))|(v2_struct_0(X24)|~v1_pre_topc(X24)|~m1_pre_topc(X24,X21))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~l1_pre_topc(X21)))&(u1_struct_0(X24)!=k2_xboole_0(u1_struct_0(X22),u1_struct_0(X23))|X24=k1_tsep_1(X21,X22,X23)|(v2_struct_0(X24)|~v1_pre_topc(X24)|~m1_pre_topc(X24,X21))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X25, X26, X27]:(((~v2_struct_0(k1_tsep_1(X25,X26,X27))|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25)))&(v1_pre_topc(k1_tsep_1(X25,X26,X27))|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25))))&(m1_pre_topc(k1_tsep_1(X25,X26,X27),X25)|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.13/0.39  fof(c_0_11, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.39  fof(c_0_12, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X13,X12)|(r2_hidden(X13,X10)|r2_hidden(X13,X11))|X12!=k2_xboole_0(X10,X11))&((~r2_hidden(X14,X10)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))&(~r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))))&(((~r2_hidden(esk2_3(X15,X16,X17),X15)|~r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16))&(~r2_hidden(esk2_3(X15,X16,X17),X16)|~r2_hidden(esk2_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16)))&(r2_hidden(esk2_3(X15,X16,X17),X17)|(r2_hidden(esk2_3(X15,X16,X17),X15)|r2_hidden(esk2_3(X15,X16,X17),X16))|X17=k2_xboole_0(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.13/0.39  cnf(c_0_13, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_15, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_16, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_17, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_19, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_21, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))|v1_xboole_0(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.39  cnf(c_0_23, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk5_0))|X1!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  cnf(c_0_32, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk6_0,k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))|v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk4_0))|X1!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_36, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (X1!=esk6_0|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))|r2_hidden(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (X1!=esk6_0|~v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_36, c_0_14])).
% 0.13/0.39  cnf(c_0_42, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (X1!=esk6_0|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk4_0))|v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.39  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_42])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.39  cnf(c_0_50, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_47])])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 53
% 0.13/0.39  # Proof object clause steps            : 40
% 0.13/0.39  # Proof object formula steps           : 13
% 0.13/0.39  # Proof object conjectures             : 26
% 0.13/0.39  # Proof object clause conjectures      : 23
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 21
% 0.13/0.39  # Proof object initial formulas used   : 6
% 0.13/0.39  # Proof object generating inferences   : 17
% 0.13/0.39  # Proof object simplifying inferences  : 21
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 6
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 27
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 27
% 0.13/0.39  # Processed clauses                    : 100
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 5
% 0.13/0.39  # ...remaining for further processing  : 94
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 5
% 0.13/0.39  # Generated clauses                    : 91
% 0.13/0.39  # ...of the previous two non-trivial   : 83
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 81
% 0.13/0.39  # Factorizations                       : 6
% 0.13/0.39  # Equation resolutions                 : 4
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 60
% 0.13/0.39  #    Positive orientable unit clauses  : 8
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 6
% 0.13/0.39  #    Non-unit-clauses                  : 46
% 0.13/0.39  # Current number of unprocessed clauses: 32
% 0.13/0.39  # ...number of literals in the above   : 146
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 34
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 783
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 356
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.39  # Unit Clause-clause subsumption calls : 43
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 2
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 3874
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.053 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.057 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

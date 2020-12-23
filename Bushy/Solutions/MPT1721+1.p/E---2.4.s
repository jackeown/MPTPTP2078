%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t30_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:13 EDT 2019

% Result     : Theorem 173.72s
% Output     : CNFRefutation 173.72s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 246 expanded)
%              Number of clauses        :   48 (  90 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 (2213 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ( m1_pre_topc(X2,X4)
                      & m1_pre_topc(X3,X4) )
                   => ( r1_tsep_1(X2,X3)
                      | m1_pre_topc(k2_tsep_1(X1,X2,X3),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',t30_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',t4_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',d5_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',dt_k2_tsep_1)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',t29_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',t1_boole)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',t1_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t30_tmap_1.p',commutativity_k3_xboole_0)).

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
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( ( m1_pre_topc(X2,X4)
                        & m1_pre_topc(X3,X4) )
                     => ( r1_tsep_1(X2,X3)
                        | m1_pre_topc(k2_tsep_1(X1,X2,X3),X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_tmap_1])).

fof(c_0_10,plain,(
    ! [X60,X61,X62] :
      ( ( ~ r1_tarski(u1_struct_0(X61),u1_struct_0(X62))
        | m1_pre_topc(X61,X62)
        | ~ m1_pre_topc(X62,X60)
        | ~ m1_pre_topc(X61,X60)
        | ~ v2_pre_topc(X60)
        | ~ l1_pre_topc(X60) )
      & ( ~ m1_pre_topc(X61,X62)
        | r1_tarski(u1_struct_0(X61),u1_struct_0(X62))
        | ~ m1_pre_topc(X62,X60)
        | ~ m1_pre_topc(X61,X60)
        | ~ v2_pre_topc(X60)
        | ~ l1_pre_topc(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & m1_pre_topc(esk2_0,esk4_0)
    & m1_pre_topc(esk3_0,esk4_0)
    & ~ r1_tsep_1(esk2_0,esk3_0)
    & ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | l1_pre_topc(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_13,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X16,X17,X18,X19] :
      ( ( X19 != k2_tsep_1(X16,X17,X18)
        | u1_struct_0(X19) = k3_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | v2_struct_0(X19)
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X16)
        | r1_tsep_1(X17,X18)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_pre_topc(X16) )
      & ( u1_struct_0(X19) != k3_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | X19 = k2_tsep_1(X16,X17,X18)
        | v2_struct_0(X19)
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X16)
        | r1_tsep_1(X17,X18)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_struct_0(k2_tsep_1(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22) )
      & ( v1_pre_topc(k2_tsep_1(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22) )
      & ( m1_pre_topc(k2_tsep_1(X22,X23,X24),X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X49,X50,X51] : r1_tarski(k3_xboole_0(X49,X50),k2_xboole_0(X49,X51)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

fof(c_0_22,plain,(
    ! [X43] : k2_xboole_0(X43,k1_xboole_0) = X43 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_23,plain,
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

cnf(c_0_24,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

fof(c_0_28,plain,(
    ! [X46,X47,X48] :
      ( ~ r1_tarski(X46,X47)
      | ~ r1_tarski(X47,X48)
      | r1_tarski(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X14,X15] : k3_xboole_0(X14,X15) = k3_xboole_0(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_35,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(esk4_0,X1,X2))
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,X2),esk1_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k2_tsep_1(esk4_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(esk1_0,X1,X2))
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_14]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_14]),c_0_15])])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,u1_struct_0(esk3_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = u1_struct_0(k2_tsep_1(esk4_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_30]),c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk4_0,esk2_0,esk3_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk4_0,esk2_0,esk3_0)) = u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_58]),c_0_51]),c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t23_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:12 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 397 expanded)
%              Number of clauses        :   31 ( 152 expanded)
%              Number of leaves         :    7 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 (2630 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tmap_1,conjecture,(
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
                 => ( m1_pre_topc(X2,X3)
                   => ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) )
                      | ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t23_tmap_1.p',t23_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t23_tmap_1.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t23_tmap_1.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t23_tmap_1.p',t4_tsep_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t23_tmap_1.p',symmetry_r1_tsep_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t23_tmap_1.p',t63_xboole_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t23_tmap_1.p',d3_tsep_1)).

fof(c_0_7,negated_conjecture,(
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
                   => ( m1_pre_topc(X2,X3)
                     => ( ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X4,X2) )
                        | ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tmap_1])).

fof(c_0_8,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & m1_pre_topc(esk2_0,esk3_0)
    & ( ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk4_0,esk2_0) )
    & ( r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(esk4_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_11,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r1_tarski(u1_struct_0(X38),u1_struct_0(X39))
        | m1_pre_topc(X38,X39)
        | ~ m1_pre_topc(X39,X37)
        | ~ m1_pre_topc(X38,X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ m1_pre_topc(X38,X39)
        | r1_tarski(u1_struct_0(X38),u1_struct_0(X39))
        | ~ m1_pre_topc(X39,X37)
        | ~ m1_pre_topc(X38,X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ~ l1_struct_0(X22)
      | ~ l1_struct_0(X23)
      | ~ r1_tsep_1(X22,X23)
      | r1_tsep_1(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_13])])).

cnf(c_0_20,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

fof(c_0_26,plain,(
    ! [X43,X44,X45] :
      ( ~ r1_tarski(X43,X44)
      | ~ r1_xboole_0(X44,X45)
      | r1_xboole_0(X43,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_13]),c_0_21])])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ( ~ r1_tsep_1(X11,X12)
        | r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X11) )
      & ( ~ r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))
        | r1_tsep_1(X11,X12)
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_31]),c_0_25]),c_0_24])])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),X1)
    | ~ r1_xboole_0(u1_struct_0(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24]),c_0_25])])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_28]),c_0_13])])).

cnf(c_0_39,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24]),c_0_41])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_43]),c_0_24]),c_0_41])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------

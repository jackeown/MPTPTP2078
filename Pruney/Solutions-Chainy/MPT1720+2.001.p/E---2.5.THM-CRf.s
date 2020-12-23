%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:05 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 794 expanded)
%              Number of clauses        :   63 ( 268 expanded)
%              Number of leaves         :   12 ( 193 expanded)
%              Depth                    :   14
%              Number of atoms          :  374 (6237 expanded)
%              Number of equality atoms :   23 (  47 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   21 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_tmap_1,conjecture,(
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X3) )
                   => m1_pre_topc(k1_tsep_1(X1,X2,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(t25_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(t22_tsep_1,axiom,(
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
             => m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(t27_tmap_1,axiom,(
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
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X4,X5) )
                       => m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

fof(t23_tsep_1,axiom,(
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
             => ( m1_pre_topc(X2,X3)
              <=> k1_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(c_0_12,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X4,X3) )
                     => m1_pre_topc(k1_tsep_1(X1,X2,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tmap_1])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_14,negated_conjecture,
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
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v2_struct_0(k1_tsep_1(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) )
      & ( v1_pre_topc(k1_tsep_1(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) )
      & ( m1_pre_topc(k1_tsep_1(X15,X16,X17),X15)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_17,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | m1_pre_topc(X31,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_22,plain,(
    ! [X32,X33,X34] :
      ( ( ~ r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | m1_pre_topc(X33,X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_pre_topc(X33,X34)
        | r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X24)
      | k1_tsep_1(X24,X25,X25) = g1_pre_topc(u1_struct_0(X25),u1_pre_topc(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

cnf(c_0_30,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_20])]),c_0_25]),c_0_26])).

fof(c_0_35,plain,(
    ! [X18,X19,X20] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ m1_pre_topc(X19,X18)
      | v2_struct_0(X20)
      | ~ m1_pre_topc(X20,X18)
      | m1_pre_topc(X19,k1_tsep_1(X18,X19,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20]),c_0_31])])).

fof(c_0_39,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X14,X12)
      | k1_tsep_1(X12,X13,X14) = k1_tsep_1(X12,X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_25])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk3_0,X1,esk3_0),esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_36]),c_0_28])]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k1_tsep_1(esk3_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_28]),c_0_38])]),c_0_25])).

fof(c_0_45,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X26)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X26)
      | v2_struct_0(X29)
      | ~ m1_pre_topc(X29,X26)
      | v2_struct_0(X30)
      | ~ m1_pre_topc(X30,X26)
      | ~ m1_pre_topc(X27,X28)
      | ~ m1_pre_topc(X29,X30)
      | m1_pre_topc(k1_tsep_1(X26,X27,X29),k1_tsep_1(X26,X28,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tmap_1])])])])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_47,plain,(
    ! [X21,X22,X23] :
      ( ( ~ m1_pre_topc(X22,X23)
        | k1_tsep_1(X21,X22,X23) = g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( k1_tsep_1(X21,X22,X23) != g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))
        | m1_pre_topc(X22,X23)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tsep_1])])])])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20]),c_0_31])])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_41]),c_0_20])])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_41]),c_0_20]),c_0_31])])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_20]),c_0_31])]),c_0_25]),c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( k1_tsep_1(esk3_0,esk3_0,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_20]),c_0_31])]),c_0_25]),c_0_26]),c_0_44])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_46]),c_0_20])])).

cnf(c_0_59,plain,
    ( k1_tsep_1(X3,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk4_0) = k1_tsep_1(esk1_0,esk4_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_20])]),c_0_49]),c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)))
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_62,negated_conjecture,
    ( m1_pre_topc(esk3_0,k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_19]),c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_36]),c_0_28]),c_0_38])])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,X3),k1_tsep_1(esk1_0,X2,esk4_0))
    | ~ m1_pre_topc(X3,esk4_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_20]),c_0_31])]),c_0_49]),c_0_26])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_19]),c_0_20]),c_0_31])]),c_0_26]),c_0_25]),c_0_44]),c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk4_0,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_19]),c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(k1_tsep_1(esk1_0,X2,esk4_0),k1_tsep_1(esk1_0,X1,esk4_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_46])]),c_0_49])).

cnf(c_0_74,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk3_0,esk4_0) = k1_tsep_1(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_46]),c_0_68]),c_0_69])]),c_0_49])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_19]),c_0_74]),c_0_25])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_78,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_46]),c_0_20])]),c_0_49]),c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_82]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_77]),c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_19]),c_0_20]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.40/0.58  # and selection function SelectComplexG.
% 0.40/0.58  #
% 0.40/0.58  # Preprocessing time       : 0.029 s
% 0.40/0.58  # Presaturation interreduction done
% 0.40/0.58  
% 0.40/0.58  # Proof found!
% 0.40/0.58  # SZS status Theorem
% 0.40/0.58  # SZS output start CNFRefutation
% 0.40/0.58  fof(t29_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 0.40/0.58  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.40/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.40/0.58  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.40/0.58  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.40/0.58  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.40/0.58  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.40/0.58  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 0.40/0.58  fof(t22_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 0.40/0.58  fof(commutativity_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k1_tsep_1)).
% 0.40/0.58  fof(t27_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X5))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tmap_1)).
% 0.40/0.58  fof(t23_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)<=>k1_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 0.40/0.58  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3))))))), inference(assume_negation,[status(cth)],[t29_tmap_1])).
% 0.40/0.58  fof(c_0_13, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.40/0.58  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((m1_pre_topc(esk2_0,esk3_0)&m1_pre_topc(esk4_0,esk3_0))&~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.40/0.58  fof(c_0_15, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.40/0.58  fof(c_0_16, plain, ![X15, X16, X17]:(((~v2_struct_0(k1_tsep_1(X15,X16,X17))|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15)))&(v1_pre_topc(k1_tsep_1(X15,X16,X17))|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15))))&(m1_pre_topc(k1_tsep_1(X15,X16,X17),X15)|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.40/0.58  fof(c_0_17, plain, ![X31]:(~l1_pre_topc(X31)|m1_pre_topc(X31,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.40/0.58  cnf(c_0_18, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.40/0.58  cnf(c_0_19, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  fof(c_0_21, plain, ![X8, X9]:(~v2_pre_topc(X8)|~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|v2_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.40/0.58  fof(c_0_22, plain, ![X32, X33, X34]:((~r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|m1_pre_topc(X33,X34)|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~m1_pre_topc(X33,X34)|r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.40/0.58  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.40/0.58  cnf(c_0_24, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.58  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_27, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.58  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.40/0.58  fof(c_0_29, plain, ![X24, X25]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X24)|k1_tsep_1(X24,X25,X25)=g1_pre_topc(u1_struct_0(X25),u1_pre_topc(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 0.40/0.58  cnf(c_0_30, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.58  cnf(c_0_31, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_32, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.40/0.58  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.40/0.58  cnf(c_0_34, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_20])]), c_0_25]), c_0_26])).
% 0.40/0.58  fof(c_0_35, plain, ![X18, X19, X20]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(v2_struct_0(X19)|~m1_pre_topc(X19,X18)|(v2_struct_0(X20)|~m1_pre_topc(X20,X18)|m1_pre_topc(X19,k1_tsep_1(X18,X19,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).
% 0.40/0.58  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.40/0.58  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.40/0.58  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_20]), c_0_31])])).
% 0.40/0.58  fof(c_0_39, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)|k1_tsep_1(X12,X13,X14)=k1_tsep_1(X12,X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).
% 0.40/0.58  cnf(c_0_40, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.40/0.58  cnf(c_0_41, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_25])).
% 0.40/0.58  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.40/0.58  cnf(c_0_43, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk3_0,X1,esk3_0),esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_36]), c_0_28])]), c_0_25])).
% 0.40/0.58  cnf(c_0_44, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k1_tsep_1(esk3_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_28]), c_0_38])]), c_0_25])).
% 0.40/0.58  fof(c_0_45, plain, ![X26, X27, X28, X29, X30]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~m1_pre_topc(X27,X26)|(v2_struct_0(X28)|~m1_pre_topc(X28,X26)|(v2_struct_0(X29)|~m1_pre_topc(X29,X26)|(v2_struct_0(X30)|~m1_pre_topc(X30,X26)|(~m1_pre_topc(X27,X28)|~m1_pre_topc(X29,X30)|m1_pre_topc(k1_tsep_1(X26,X27,X29),k1_tsep_1(X26,X28,X30)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tmap_1])])])])).
% 0.40/0.58  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  fof(c_0_47, plain, ![X21, X22, X23]:((~m1_pre_topc(X22,X23)|k1_tsep_1(X21,X22,X23)=g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(k1_tsep_1(X21,X22,X23)!=g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23))|m1_pre_topc(X22,X23)|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tsep_1])])])])])).
% 0.40/0.58  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.40/0.58  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_50, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.40/0.58  cnf(c_0_51, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_20]), c_0_31])])).
% 0.40/0.58  cnf(c_0_52, negated_conjecture, (l1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_41]), c_0_20])])).
% 0.40/0.58  cnf(c_0_53, negated_conjecture, (v2_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_41]), c_0_20]), c_0_31])])).
% 0.40/0.58  cnf(c_0_54, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk3_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_20]), c_0_31])]), c_0_25]), c_0_26])).
% 0.40/0.58  cnf(c_0_55, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk3_0,esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_36]), c_0_25])).
% 0.40/0.58  cnf(c_0_56, negated_conjecture, (k1_tsep_1(esk3_0,esk3_0,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_20]), c_0_31])]), c_0_25]), c_0_26]), c_0_44])).
% 0.40/0.58  cnf(c_0_57, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X5)|m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X5,X1)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.40/0.58  cnf(c_0_58, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_46]), c_0_20])])).
% 0.40/0.58  cnf(c_0_59, plain, (k1_tsep_1(X3,X1,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.40/0.58  cnf(c_0_60, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk4_0)=k1_tsep_1(esk1_0,esk4_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_20])]), c_0_49]), c_0_26])).
% 0.40/0.58  cnf(c_0_61, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)))|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.40/0.58  cnf(c_0_62, negated_conjecture, (m1_pre_topc(esk3_0,k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_19]), c_0_25])).
% 0.40/0.58  cnf(c_0_63, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_36]), c_0_28]), c_0_38])])).
% 0.40/0.58  cnf(c_0_64, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.40/0.58  cnf(c_0_65, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(k1_tsep_1(esk1_0,X1,X3),k1_tsep_1(esk1_0,X2,esk4_0))|~m1_pre_topc(X3,esk4_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_20]), c_0_31])]), c_0_49]), c_0_26])).
% 0.40/0.58  cnf(c_0_66, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_58])).
% 0.40/0.58  cnf(c_0_67, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_19]), c_0_20]), c_0_31])]), c_0_26]), c_0_25]), c_0_44]), c_0_56])).
% 0.40/0.58  cnf(c_0_68, negated_conjecture, (k1_tsep_1(esk1_0,esk4_0,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_19]), c_0_25])).
% 0.40/0.58  cnf(c_0_69, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_70, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.40/0.58  cnf(c_0_71, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.40/0.58  cnf(c_0_72, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.40/0.58  cnf(c_0_73, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(k1_tsep_1(esk1_0,X2,esk4_0),k1_tsep_1(esk1_0,X1,esk4_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_46])]), c_0_49])).
% 0.40/0.58  cnf(c_0_74, negated_conjecture, (k1_tsep_1(esk1_0,esk3_0,esk4_0)=k1_tsep_1(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_46]), c_0_68]), c_0_69])]), c_0_49])).
% 0.40/0.58  cnf(c_0_75, negated_conjecture, (u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.40/0.58  cnf(c_0_76, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_19]), c_0_74]), c_0_25])).
% 0.40/0.58  cnf(c_0_77, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_78, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_79, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_80, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[c_0_61, c_0_75])).
% 0.40/0.58  cnf(c_0_81, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), c_0_79])).
% 0.40/0.58  cnf(c_0_82, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.40/0.58  cnf(c_0_83, negated_conjecture, (~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.58  cnf(c_0_84, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_46]), c_0_20])]), c_0_49]), c_0_26])).
% 0.40/0.58  cnf(c_0_85, negated_conjecture, (~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_82]), c_0_83])).
% 0.40/0.58  cnf(c_0_86, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_77]), c_0_79])).
% 0.40/0.58  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_19]), c_0_20]), c_0_31])]), ['proof']).
% 0.40/0.58  # SZS output end CNFRefutation
% 0.40/0.58  # Proof object total steps             : 88
% 0.40/0.58  # Proof object clause steps            : 63
% 0.40/0.58  # Proof object formula steps           : 25
% 0.40/0.58  # Proof object conjectures             : 51
% 0.40/0.58  # Proof object clause conjectures      : 48
% 0.40/0.58  # Proof object formula conjectures     : 3
% 0.40/0.58  # Proof object initial clauses used    : 25
% 0.40/0.58  # Proof object initial formulas used   : 12
% 0.40/0.58  # Proof object generating inferences   : 35
% 0.40/0.58  # Proof object simplifying inferences  : 90
% 0.40/0.58  # Training examples: 0 positive, 0 negative
% 0.40/0.58  # Parsed axioms                        : 12
% 0.40/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.58  # Initial clauses                      : 29
% 0.40/0.58  # Removed in clause preprocessing      : 0
% 0.40/0.58  # Initial clauses in saturation        : 29
% 0.40/0.58  # Processed clauses                    : 2098
% 0.40/0.58  # ...of these trivial                  : 82
% 0.40/0.58  # ...subsumed                          : 292
% 0.40/0.58  # ...remaining for further processing  : 1724
% 0.40/0.58  # Other redundant clauses eliminated   : 2
% 0.40/0.58  # Clauses deleted for lack of memory   : 0
% 0.40/0.58  # Backward-subsumed                    : 8
% 0.40/0.58  # Backward-rewritten                   : 564
% 0.40/0.58  # Generated clauses                    : 13476
% 0.40/0.58  # ...of the previous two non-trivial   : 12476
% 0.40/0.58  # Contextual simplify-reflections      : 4
% 0.40/0.58  # Paramodulations                      : 13474
% 0.40/0.58  # Factorizations                       : 0
% 0.40/0.58  # Equation resolutions                 : 2
% 0.40/0.58  # Propositional unsat checks           : 0
% 0.40/0.58  #    Propositional check models        : 0
% 0.40/0.58  #    Propositional check unsatisfiable : 0
% 0.40/0.58  #    Propositional clauses             : 0
% 0.40/0.58  #    Propositional clauses after purity: 0
% 0.40/0.58  #    Propositional unsat core size     : 0
% 0.40/0.58  #    Propositional preprocessing time  : 0.000
% 0.40/0.58  #    Propositional encoding time       : 0.000
% 0.40/0.58  #    Propositional solver time         : 0.000
% 0.40/0.58  #    Success case prop preproc time    : 0.000
% 0.40/0.58  #    Success case prop encoding time   : 0.000
% 0.40/0.58  #    Success case prop solver time     : 0.000
% 0.40/0.58  # Current number of processed clauses  : 1122
% 0.40/0.58  #    Positive orientable unit clauses  : 656
% 0.40/0.58  #    Positive unorientable unit clauses: 0
% 0.40/0.58  #    Negative unit clauses             : 32
% 0.40/0.58  #    Non-unit-clauses                  : 434
% 0.40/0.58  # Current number of unprocessed clauses: 9725
% 0.40/0.58  # ...number of literals in the above   : 26686
% 0.40/0.58  # Current number of archived formulas  : 0
% 0.40/0.58  # Current number of archived clauses   : 600
% 0.40/0.58  # Clause-clause subsumption calls (NU) : 27177
% 0.40/0.58  # Rec. Clause-clause subsumption calls : 12082
% 0.40/0.58  # Non-unit clause-clause subsumptions  : 186
% 0.40/0.58  # Unit Clause-clause subsumption calls : 7244
% 0.40/0.58  # Rewrite failures with RHS unbound    : 0
% 0.40/0.58  # BW rewrite match attempts            : 6138
% 0.40/0.58  # BW rewrite match successes           : 107
% 0.40/0.58  # Condensation attempts                : 0
% 0.40/0.58  # Condensation successes               : 0
% 0.40/0.58  # Termbank termtop insertions          : 480060
% 0.40/0.59  
% 0.40/0.59  # -------------------------------------------------
% 0.40/0.59  # User time                : 0.233 s
% 0.40/0.59  # System time              : 0.014 s
% 0.40/0.59  # Total time               : 0.247 s
% 0.40/0.59  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

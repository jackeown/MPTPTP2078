%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:05 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 298 expanded)
%              Number of clauses        :   40 (  92 expanded)
%              Number of leaves         :    6 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  334 (3359 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_tmap_1,conjecture,(
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
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X3,X5) )
                       => ( r1_tsep_1(X2,X3)
                          | m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

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

fof(t24_tmap_1,axiom,(
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
                   => ( ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) )
                      | ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(t27_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

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
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X2,X4)
                            & m1_pre_topc(X3,X5) )
                         => ( r1_tsep_1(X2,X3)
                            | m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X5)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_tmap_1])).

fof(c_0_7,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r1_tarski(u1_struct_0(X22),u1_struct_0(X23))
        | m1_pre_topc(X22,X23)
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_pre_topc(X22,X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_pre_topc(X22,X23)
        | r1_tarski(u1_struct_0(X22),u1_struct_0(X23))
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_pre_topc(X22,X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v2_struct_0(k2_tsep_1(X14,X15,X16))
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X14) )
      & ( v1_pre_topc(k2_tsep_1(X14,X15,X16))
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X14) )
      & ( m1_pre_topc(k2_tsep_1(X14,X15,X16),X14)
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X14)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

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
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk2_0,esk4_0)
    & m1_pre_topc(esk3_0,esk5_0)
    & ~ r1_tsep_1(esk2_0,esk3_0)
    & ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13] :
      ( ( X13 != k2_tsep_1(X10,X11,X12)
        | u1_struct_0(X13) = k3_xboole_0(u1_struct_0(X11),u1_struct_0(X12))
        | v2_struct_0(X13)
        | ~ v1_pre_topc(X13)
        | ~ m1_pre_topc(X13,X10)
        | r1_tsep_1(X11,X12)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10) )
      & ( u1_struct_0(X13) != k3_xboole_0(u1_struct_0(X11),u1_struct_0(X12))
        | X13 = k2_tsep_1(X10,X11,X12)
        | v2_struct_0(X13)
        | ~ v1_pre_topc(X13)
        | ~ m1_pre_topc(X13,X10)
        | r1_tsep_1(X11,X12)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

fof(c_0_13,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r1_tsep_1(X18,X20)
        | ~ r1_tsep_1(X19,X20)
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tsep_1(X20,X18)
        | ~ r1_tsep_1(X19,X20)
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tsep_1(X18,X20)
        | ~ r1_tsep_1(X20,X19)
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tsep_1(X20,X18)
        | ~ r1_tsep_1(X20,X19)
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_pre_topc(X1,k2_tsep_1(X2,X3,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(k2_tsep_1(X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X3,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_11]),c_0_24]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_16]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_19])]),c_0_31]),c_0_20]),c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(esk5_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_16]),c_0_19])]),c_0_20]),c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30])]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_41,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk5_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29])]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_17])]),c_0_22])).

fof(c_0_44,plain,(
    ! [X6,X7,X8,X9] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(k3_xboole_0(X6,X8),k3_xboole_0(X7,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_17]),c_0_16]),c_0_19])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_18]),c_0_16]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_29])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_30])])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_11]),c_0_29]),c_0_30]),c_0_19])]),c_0_33]),c_0_32]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t28_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X4)&m1_pre_topc(X3,X5))=>(r1_tsep_1(X2,X3)|m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tmap_1)).
% 0.20/0.39  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.39  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.20/0.39  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.20/0.39  fof(t24_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 0.20/0.39  fof(t27_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 0.20/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X4)&m1_pre_topc(X3,X5))=>(r1_tsep_1(X2,X3)|m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X5)))))))))), inference(assume_negation,[status(cth)],[t28_tmap_1])).
% 0.20/0.39  fof(c_0_7, plain, ![X21, X22, X23]:((~r1_tarski(u1_struct_0(X22),u1_struct_0(X23))|m1_pre_topc(X22,X23)|~m1_pre_topc(X23,X21)|~m1_pre_topc(X22,X21)|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~m1_pre_topc(X22,X23)|r1_tarski(u1_struct_0(X22),u1_struct_0(X23))|~m1_pre_topc(X23,X21)|~m1_pre_topc(X22,X21)|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.39  fof(c_0_8, plain, ![X14, X15, X16]:(((~v2_struct_0(k2_tsep_1(X14,X15,X16))|(v2_struct_0(X14)|~l1_pre_topc(X14)|v2_struct_0(X15)|~m1_pre_topc(X15,X14)|v2_struct_0(X16)|~m1_pre_topc(X16,X14)))&(v1_pre_topc(k2_tsep_1(X14,X15,X16))|(v2_struct_0(X14)|~l1_pre_topc(X14)|v2_struct_0(X15)|~m1_pre_topc(X15,X14)|v2_struct_0(X16)|~m1_pre_topc(X16,X14))))&(m1_pre_topc(k2_tsep_1(X14,X15,X16),X14)|(v2_struct_0(X14)|~l1_pre_topc(X14)|v2_struct_0(X15)|~m1_pre_topc(X15,X14)|v2_struct_0(X16)|~m1_pre_topc(X16,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.20/0.39  fof(c_0_9, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((m1_pre_topc(esk2_0,esk4_0)&m1_pre_topc(esk3_0,esk5_0))&(~r1_tsep_1(esk2_0,esk3_0)&~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.20/0.39  cnf(c_0_10, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_11, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  fof(c_0_12, plain, ![X10, X11, X12, X13]:((X13!=k2_tsep_1(X10,X11,X12)|u1_struct_0(X13)=k3_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|(v2_struct_0(X13)|~v1_pre_topc(X13)|~m1_pre_topc(X13,X10))|r1_tsep_1(X11,X12)|(v2_struct_0(X12)|~m1_pre_topc(X12,X10))|(v2_struct_0(X11)|~m1_pre_topc(X11,X10))|(v2_struct_0(X10)|~l1_pre_topc(X10)))&(u1_struct_0(X13)!=k3_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|X13=k2_tsep_1(X10,X11,X12)|(v2_struct_0(X13)|~v1_pre_topc(X13)|~m1_pre_topc(X13,X10))|r1_tsep_1(X11,X12)|(v2_struct_0(X12)|~m1_pre_topc(X12,X10))|(v2_struct_0(X11)|~m1_pre_topc(X11,X10))|(v2_struct_0(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.20/0.39  fof(c_0_13, plain, ![X17, X18, X19, X20]:(((r1_tsep_1(X18,X20)|~r1_tsep_1(X19,X20)|~m1_pre_topc(X18,X19)|(v2_struct_0(X20)|~m1_pre_topc(X20,X17))|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(r1_tsep_1(X20,X18)|~r1_tsep_1(X19,X20)|~m1_pre_topc(X18,X19)|(v2_struct_0(X20)|~m1_pre_topc(X20,X17))|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&((r1_tsep_1(X18,X20)|~r1_tsep_1(X20,X19)|~m1_pre_topc(X18,X19)|(v2_struct_0(X20)|~m1_pre_topc(X20,X17))|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(r1_tsep_1(X20,X18)|~r1_tsep_1(X20,X19)|~m1_pre_topc(X18,X19)|(v2_struct_0(X20)|~m1_pre_topc(X20,X17))|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_15, plain, (m1_pre_topc(X1,k2_tsep_1(X2,X3,X4))|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(k2_tsep_1(X2,X3,X4)))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_23, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_24, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_26, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X4)|~r1_tsep_1(X3,X1)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X3,X4)|~m1_pre_topc(X2,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)|~r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.39  cnf(c_0_28, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_11]), c_0_24]), c_0_25])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(esk4_0,X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_16]), c_0_19])]), c_0_20]), c_0_21])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)|~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_19])]), c_0_31]), c_0_20]), c_0_32]), c_0_33])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(esk5_0,X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_16]), c_0_19])]), c_0_20]), c_0_22])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_30])]), c_0_32])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (r1_tsep_1(esk4_0,esk5_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)|~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_17]), c_0_18]), c_0_19])]), c_0_20]), c_0_21]), c_0_22])).
% 0.20/0.39  cnf(c_0_41, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~r1_tsep_1(esk5_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_29])]), c_0_33])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (r1_tsep_1(esk5_0,esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)|~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_17])]), c_0_22])).
% 0.20/0.39  fof(c_0_44, plain, ![X6, X7, X8, X9]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X9)|r1_tarski(k3_xboole_0(X6,X8),k3_xboole_0(X7,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_xboole_1])])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_17]), c_0_16]), c_0_19])])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_18]), c_0_16]), c_0_19])])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)|~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_30])]), c_0_31]), c_0_32])).
% 0.20/0.39  cnf(c_0_48, plain, (r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_29])])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_30])])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_11]), c_0_29]), c_0_30]), c_0_19])]), c_0_33]), c_0_32]), c_0_20]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 53
% 0.20/0.39  # Proof object clause steps            : 40
% 0.20/0.39  # Proof object formula steps           : 13
% 0.20/0.39  # Proof object conjectures             : 33
% 0.20/0.39  # Proof object clause conjectures      : 30
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 23
% 0.20/0.39  # Proof object initial formulas used   : 6
% 0.20/0.39  # Proof object generating inferences   : 16
% 0.20/0.39  # Proof object simplifying inferences  : 70
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 6
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 27
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 27
% 0.20/0.39  # Processed clauses                    : 136
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 8
% 0.20/0.39  # ...remaining for further processing  : 128
% 0.20/0.39  # Other redundant clauses eliminated   : 1
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 6
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 176
% 0.20/0.39  # ...of the previous two non-trivial   : 170
% 0.20/0.39  # Contextual simplify-reflections      : 6
% 0.20/0.39  # Paramodulations                      : 175
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 1
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
% 0.20/0.39  # Current number of processed clauses  : 94
% 0.20/0.39  #    Positive orientable unit clauses  : 10
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 8
% 0.20/0.39  #    Non-unit-clauses                  : 76
% 0.20/0.39  # Current number of unprocessed clauses: 87
% 0.20/0.39  # ...number of literals in the above   : 963
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 33
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2692
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 358
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 20
% 0.20/0.39  # Unit Clause-clause subsumption calls : 48
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 8969
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.042 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.048 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

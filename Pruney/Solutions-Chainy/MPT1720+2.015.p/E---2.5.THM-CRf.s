%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:07 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 310 expanded)
%              Number of clauses        :   44 (  99 expanded)
%              Number of leaves         :    8 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  337 (2763 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   22 (   3 average)
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

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ m1_pre_topc(X19,X18)
      | k1_tsep_1(X18,X19,X19) = g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

fof(c_0_10,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X11 != k1_tsep_1(X8,X9,X10)
        | u1_struct_0(X11) = k2_xboole_0(u1_struct_0(X9),u1_struct_0(X10))
        | v2_struct_0(X11)
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) )
      & ( u1_struct_0(X11) != k2_xboole_0(u1_struct_0(X9),u1_struct_0(X10))
        | X11 = k1_tsep_1(X8,X9,X10)
        | v2_struct_0(X11)
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v2_struct_0(k1_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( v1_pre_topc(k1_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( m1_pre_topc(k1_tsep_1(X12,X13,X14),X12)
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] :
      ( ( ~ m1_pre_topc(X16,X17)
        | k1_tsep_1(X15,X16,X17) = g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( k1_tsep_1(X15,X16,X17) != g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))
        | m1_pre_topc(X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tsep_1])])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r1_tarski(u1_struct_0(X26),u1_struct_0(X27))
        | m1_pre_topc(X26,X27)
        | ~ m1_pre_topc(X27,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ m1_pre_topc(X26,X27)
        | r1_tarski(u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_pre_topc(X27,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( k1_tsep_1(X3,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k1_tsep_1(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

fof(c_0_27,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,X20)
      | v2_struct_0(X22)
      | ~ m1_pre_topc(X22,X20)
      | v2_struct_0(X23)
      | ~ m1_pre_topc(X23,X20)
      | v2_struct_0(X24)
      | ~ m1_pre_topc(X24,X20)
      | ~ m1_pre_topc(X21,X22)
      | ~ m1_pre_topc(X23,X24)
      | m1_pre_topc(k1_tsep_1(X20,X21,X23),k1_tsep_1(X20,X22,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tmap_1])])])])).

cnf(c_0_28,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_26]),c_0_16]),c_0_17])]),c_0_19]),c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_17])]),c_0_18]),c_0_19])).

fof(c_0_36,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_17])]),c_0_19]),c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk4_0,esk3_0) = k1_tsep_1(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,X2),k1_tsep_1(esk1_0,X3,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_15]),c_0_18])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_32])])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) = u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_39]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),k1_tsep_1(esk1_0,X2,esk3_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_31])]),c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)))
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_41]),c_0_16]),c_0_17])])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_15]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_31]),c_0_17])]),c_0_33]),c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_51])).

cnf(c_0_56,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_16]),c_0_15]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:00:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.68  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.47/0.68  # and selection function SelectComplexG.
% 0.47/0.68  #
% 0.47/0.68  # Preprocessing time       : 0.028 s
% 0.47/0.68  # Presaturation interreduction done
% 0.47/0.68  
% 0.47/0.68  # Proof found!
% 0.47/0.68  # SZS status Theorem
% 0.47/0.68  # SZS output start CNFRefutation
% 0.47/0.68  fof(t29_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 0.47/0.68  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 0.47/0.68  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.47/0.68  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.47/0.68  fof(t23_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)<=>k1_tsep_1(X1,X2,X3)=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 0.47/0.68  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.47/0.68  fof(t27_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X5))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tmap_1)).
% 0.47/0.68  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.47/0.68  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X3))=>m1_pre_topc(k1_tsep_1(X1,X2,X4),X3))))))), inference(assume_negation,[status(cth)],[t29_tmap_1])).
% 0.47/0.68  fof(c_0_9, plain, ![X18, X19]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(v2_struct_0(X19)|~m1_pre_topc(X19,X18)|k1_tsep_1(X18,X19,X19)=g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 0.47/0.68  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((m1_pre_topc(esk2_0,esk3_0)&m1_pre_topc(esk4_0,esk3_0))&~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.47/0.68  fof(c_0_11, plain, ![X8, X9, X10, X11]:((X11!=k1_tsep_1(X8,X9,X10)|u1_struct_0(X11)=k2_xboole_0(u1_struct_0(X9),u1_struct_0(X10))|(v2_struct_0(X11)|~v1_pre_topc(X11)|~m1_pre_topc(X11,X8))|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~l1_pre_topc(X8)))&(u1_struct_0(X11)!=k2_xboole_0(u1_struct_0(X9),u1_struct_0(X10))|X11=k1_tsep_1(X8,X9,X10)|(v2_struct_0(X11)|~v1_pre_topc(X11)|~m1_pre_topc(X11,X8))|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~l1_pre_topc(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.47/0.68  fof(c_0_12, plain, ![X12, X13, X14]:(((~v2_struct_0(k1_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))&(v1_pre_topc(k1_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12))))&(m1_pre_topc(k1_tsep_1(X12,X13,X14),X12)|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.47/0.68  fof(c_0_13, plain, ![X15, X16, X17]:((~m1_pre_topc(X16,X17)|k1_tsep_1(X15,X16,X17)=g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(k1_tsep_1(X15,X16,X17)!=g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))|m1_pre_topc(X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tsep_1])])])])])).
% 0.47/0.68  cnf(c_0_14, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.47/0.68  cnf(c_0_15, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  fof(c_0_20, plain, ![X25, X26, X27]:((~r1_tarski(u1_struct_0(X26),u1_struct_0(X27))|m1_pre_topc(X26,X27)|~m1_pre_topc(X27,X25)|~m1_pre_topc(X26,X25)|(~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~m1_pre_topc(X26,X27)|r1_tarski(u1_struct_0(X26),u1_struct_0(X27))|~m1_pre_topc(X27,X25)|~m1_pre_topc(X26,X25)|(~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.47/0.68  cnf(c_0_21, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.68  cnf(c_0_22, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.68  cnf(c_0_23, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.68  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.68  cnf(c_0_25, plain, (k1_tsep_1(X3,X1,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.68  cnf(c_0_26, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k1_tsep_1(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.47/0.68  fof(c_0_27, plain, ![X20, X21, X22, X23, X24]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X20)|(v2_struct_0(X22)|~m1_pre_topc(X22,X20)|(v2_struct_0(X23)|~m1_pre_topc(X23,X20)|(v2_struct_0(X24)|~m1_pre_topc(X24,X20)|(~m1_pre_topc(X21,X22)|~m1_pre_topc(X23,X24)|m1_pre_topc(k1_tsep_1(X20,X21,X23),k1_tsep_1(X20,X22,X24)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tmap_1])])])])).
% 0.47/0.68  cnf(c_0_28, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.68  cnf(c_0_29, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.47/0.68  cnf(c_0_30, negated_conjecture, (k1_tsep_1(esk1_0,X1,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_26]), c_0_16]), c_0_17])]), c_0_19]), c_0_18])).
% 0.47/0.68  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X5)|m1_pre_topc(k1_tsep_1(X1,X2,X4),k1_tsep_1(X1,X3,X5))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X5,X1)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.68  cnf(c_0_35, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk3_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_15]), c_0_17])]), c_0_18]), c_0_19])).
% 0.47/0.68  fof(c_0_36, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.47/0.68  cnf(c_0_37, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_15]), c_0_16]), c_0_17])])).
% 0.47/0.68  cnf(c_0_38, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_15]), c_0_17])]), c_0_19]), c_0_18])).
% 0.47/0.68  cnf(c_0_39, negated_conjecture, (k1_tsep_1(esk1_0,esk4_0,esk3_0)=k1_tsep_1(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.47/0.68  cnf(c_0_40, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,X2),k1_tsep_1(esk1_0,X3,esk3_0))|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.47/0.68  cnf(c_0_41, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_15]), c_0_18])).
% 0.47/0.68  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.68  cnf(c_0_43, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_32])])).
% 0.47/0.68  cnf(c_0_44, negated_conjecture, (k2_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))=u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_39]), c_0_33])).
% 0.47/0.68  cnf(c_0_45, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),k1_tsep_1(esk1_0,X2,esk3_0))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_31])]), c_0_33])).
% 0.47/0.68  cnf(c_0_46, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0)))|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_41]), c_0_16]), c_0_17])])).
% 0.47/0.68  cnf(c_0_47, negated_conjecture, (u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk3_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.47/0.68  cnf(c_0_48, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_15]), c_0_18])).
% 0.47/0.68  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_52, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_31]), c_0_17])]), c_0_33]), c_0_19])).
% 0.47/0.68  cnf(c_0_53, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,k1_tsep_1(esk1_0,esk3_0,esk3_0))|~m1_pre_topc(X1,esk1_0)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.47/0.68  cnf(c_0_54, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),k1_tsep_1(esk1_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), c_0_51])).
% 0.47/0.68  cnf(c_0_55, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_51])).
% 0.47/0.68  cnf(c_0_56, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.68  cnf(c_0_57, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.47/0.68  cnf(c_0_58, negated_conjecture, (~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.68  cnf(c_0_59, negated_conjecture, (~v2_pre_topc(X1)|~m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.47/0.68  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_55]), c_0_16]), c_0_15]), c_0_17])]), ['proof']).
% 0.47/0.68  # SZS output end CNFRefutation
% 0.47/0.68  # Proof object total steps             : 61
% 0.47/0.68  # Proof object clause steps            : 44
% 0.47/0.68  # Proof object formula steps           : 17
% 0.47/0.68  # Proof object conjectures             : 36
% 0.47/0.68  # Proof object clause conjectures      : 33
% 0.47/0.68  # Proof object formula conjectures     : 3
% 0.47/0.68  # Proof object initial clauses used    : 22
% 0.47/0.68  # Proof object initial formulas used   : 8
% 0.47/0.68  # Proof object generating inferences   : 20
% 0.47/0.68  # Proof object simplifying inferences  : 63
% 0.47/0.68  # Training examples: 0 positive, 0 negative
% 0.47/0.68  # Parsed axioms                        : 8
% 0.47/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.68  # Initial clauses                      : 24
% 0.47/0.68  # Removed in clause preprocessing      : 0
% 0.47/0.68  # Initial clauses in saturation        : 24
% 0.47/0.68  # Processed clauses                    : 1515
% 0.47/0.68  # ...of these trivial                  : 19
% 0.47/0.68  # ...subsumed                          : 31
% 0.47/0.68  # ...remaining for further processing  : 1465
% 0.47/0.68  # Other redundant clauses eliminated   : 1
% 0.47/0.68  # Clauses deleted for lack of memory   : 0
% 0.47/0.68  # Backward-subsumed                    : 31
% 0.47/0.68  # Backward-rewritten                   : 529
% 0.47/0.68  # Generated clauses                    : 17019
% 0.47/0.68  # ...of the previous two non-trivial   : 17011
% 0.47/0.68  # Contextual simplify-reflections      : 6
% 0.47/0.68  # Paramodulations                      : 17014
% 0.47/0.68  # Factorizations                       : 0
% 0.47/0.68  # Equation resolutions                 : 5
% 0.47/0.68  # Propositional unsat checks           : 0
% 0.47/0.68  #    Propositional check models        : 0
% 0.47/0.68  #    Propositional check unsatisfiable : 0
% 0.47/0.68  #    Propositional clauses             : 0
% 0.47/0.68  #    Propositional clauses after purity: 0
% 0.47/0.68  #    Propositional unsat core size     : 0
% 0.47/0.68  #    Propositional preprocessing time  : 0.000
% 0.47/0.68  #    Propositional encoding time       : 0.000
% 0.47/0.68  #    Propositional solver time         : 0.000
% 0.47/0.68  #    Success case prop preproc time    : 0.000
% 0.47/0.68  #    Success case prop encoding time   : 0.000
% 0.47/0.68  #    Success case prop solver time     : 0.000
% 0.47/0.68  # Current number of processed clauses  : 880
% 0.47/0.68  #    Positive orientable unit clauses  : 318
% 0.47/0.68  #    Positive unorientable unit clauses: 0
% 0.47/0.68  #    Negative unit clauses             : 6
% 0.47/0.68  #    Non-unit-clauses                  : 556
% 0.47/0.68  # Current number of unprocessed clauses: 15355
% 0.47/0.68  # ...number of literals in the above   : 48669
% 0.47/0.68  # Current number of archived formulas  : 0
% 0.47/0.68  # Current number of archived clauses   : 584
% 0.47/0.68  # Clause-clause subsumption calls (NU) : 60441
% 0.47/0.68  # Rec. Clause-clause subsumption calls : 40195
% 0.47/0.68  # Non-unit clause-clause subsumptions  : 61
% 0.47/0.68  # Unit Clause-clause subsumption calls : 3537
% 0.47/0.68  # Rewrite failures with RHS unbound    : 0
% 0.47/0.68  # BW rewrite match attempts            : 15427
% 0.47/0.68  # BW rewrite match successes           : 281
% 0.47/0.68  # Condensation attempts                : 0
% 0.47/0.68  # Condensation successes               : 0
% 0.47/0.68  # Termbank termtop insertions          : 693705
% 0.47/0.68  
% 0.47/0.68  # -------------------------------------------------
% 0.47/0.68  # User time                : 0.320 s
% 0.47/0.68  # System time              : 0.017 s
% 0.47/0.68  # Total time               : 0.337 s
% 0.47/0.68  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

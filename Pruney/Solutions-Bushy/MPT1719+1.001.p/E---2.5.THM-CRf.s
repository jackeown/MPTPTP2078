%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1719+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:39 EST 2020

% Result     : Theorem 0.06s
% Output     : CNFRefutation 0.06s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 351 expanded)
%              Number of clauses        :   61 ( 123 expanded)
%              Number of leaves         :   10 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  334 (3321 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t27_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_10,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X11 != k2_tsep_1(X8,X9,X10)
        | u1_struct_0(X11) = k3_xboole_0(u1_struct_0(X9),u1_struct_0(X10))
        | v2_struct_0(X11)
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X8)
        | r1_tsep_1(X9,X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) )
      & ( u1_struct_0(X11) != k3_xboole_0(u1_struct_0(X9),u1_struct_0(X10))
        | X11 = k2_tsep_1(X8,X9,X10)
        | v2_struct_0(X11)
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X8)
        | r1_tsep_1(X9,X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

fof(c_0_11,plain,(
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
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X2,X4)
                            & m1_pre_topc(X3,X5) )
                         => ( r1_tsep_1(X2,X3)
                            | m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X5)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_tmap_1])).

fof(c_0_13,plain,(
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

cnf(c_0_14,plain,
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

cnf(c_0_15,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_20,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_27,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X1,k2_tsep_1(X2,X3,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(k2_tsep_1(X2,X3,X4)))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | r1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_35,plain,(
    ! [X6,X7] :
      ( ( ~ r1_tsep_1(X6,X7)
        | r1_xboole_0(u1_struct_0(X6),u1_struct_0(X7))
        | ~ l1_struct_0(X7)
        | ~ l1_struct_0(X6) )
      & ( ~ r1_xboole_0(u1_struct_0(X6),u1_struct_0(X7))
        | r1_tsep_1(X6,X7)
        | ~ l1_struct_0(X7)
        | ~ l1_struct_0(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23])])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),k2_tsep_1(esk1_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(X1,k2_tsep_1(esk1_0,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(k2_tsep_1(esk1_0,X2,X3)))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23])]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) = k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,X1,esk5_0)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | r1_tsep_1(X1,esk5_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_28]),c_0_23])]),c_0_24]),c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_39]),c_0_23])])).

fof(c_0_48,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k3_xboole_0(X12,X13) = k1_xboole_0 )
      & ( k3_xboole_0(X12,X13) != k1_xboole_0
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk5_0)))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_28]),c_0_39])]),c_0_36]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,X1,esk5_0)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_39]),c_0_51])]),c_0_43])).

fof(c_0_55,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k3_xboole_0(X20,X22),k3_xboole_0(X21,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_xboole_1])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_28]),c_0_30]),c_0_23])])).

cnf(c_0_57,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_39]),c_0_30]),c_0_23])])).

cnf(c_0_59,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) = k1_xboole_0
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_22])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_33])])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) = k1_xboole_0
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_65,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X2,u1_struct_0(esk5_0))
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_65])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_23])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,u1_struct_0(esk3_0)),k1_xboole_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) != k1_xboole_0
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33]),c_0_23])])).

fof(c_0_74,plain,(
    ! [X24] :
      ( ~ r1_tarski(X24,k1_xboole_0)
      | X24 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k1_xboole_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) != k1_xboole_0
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_73])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_15]),c_0_22]),c_0_33]),c_0_23])]),c_0_25]),c_0_34]),c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),
    [proof]).

%------------------------------------------------------------------------------

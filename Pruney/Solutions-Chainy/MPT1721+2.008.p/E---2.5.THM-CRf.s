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
% DateTime   : Thu Dec  3 11:17:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 125 expanded)
%              Number of clauses        :   29 (  41 expanded)
%              Number of leaves         :    6 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  217 (1162 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   18 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_6,plain,(
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

fof(c_0_7,plain,(
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
                   => ( ( m1_pre_topc(X2,X4)
                        & m1_pre_topc(X3,X4) )
                     => ( r1_tsep_1(X2,X3)
                        | m1_pre_topc(k2_tsep_1(X1,X2,X3),X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_tmap_1])).

cnf(c_0_9,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r1_tarski(u1_struct_0(X18),u1_struct_0(X19))
        | m1_pre_topc(X18,X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_pre_topc(X18,X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_pre_topc(X18,X19)
        | r1_tarski(u1_struct_0(X18),u1_struct_0(X19))
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_pre_topc(X18,X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_15,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_17])])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) = k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_31,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_22]),c_0_17])])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25])])).

fof(c_0_37,plain,(
    ! [X5,X6] : r1_tarski(k3_xboole_0(X5,X6),X5) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_10]),c_0_16]),c_0_25]),c_0_17])]),c_0_19]),c_0_26]),c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.19/0.37  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.19/0.37  fof(t30_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X4)&m1_pre_topc(X3,X4))=>(r1_tsep_1(X2,X3)|m1_pre_topc(k2_tsep_1(X1,X2,X3),X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 0.19/0.37  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.19/0.37  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.37  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.37  fof(c_0_6, plain, ![X10, X11, X12, X13]:((X13!=k2_tsep_1(X10,X11,X12)|u1_struct_0(X13)=k3_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|(v2_struct_0(X13)|~v1_pre_topc(X13)|~m1_pre_topc(X13,X10))|r1_tsep_1(X11,X12)|(v2_struct_0(X12)|~m1_pre_topc(X12,X10))|(v2_struct_0(X11)|~m1_pre_topc(X11,X10))|(v2_struct_0(X10)|~l1_pre_topc(X10)))&(u1_struct_0(X13)!=k3_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|X13=k2_tsep_1(X10,X11,X12)|(v2_struct_0(X13)|~v1_pre_topc(X13)|~m1_pre_topc(X13,X10))|r1_tsep_1(X11,X12)|(v2_struct_0(X12)|~m1_pre_topc(X12,X10))|(v2_struct_0(X11)|~m1_pre_topc(X11,X10))|(v2_struct_0(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X14, X15, X16]:(((~v2_struct_0(k2_tsep_1(X14,X15,X16))|(v2_struct_0(X14)|~l1_pre_topc(X14)|v2_struct_0(X15)|~m1_pre_topc(X15,X14)|v2_struct_0(X16)|~m1_pre_topc(X16,X14)))&(v1_pre_topc(k2_tsep_1(X14,X15,X16))|(v2_struct_0(X14)|~l1_pre_topc(X14)|v2_struct_0(X15)|~m1_pre_topc(X15,X14)|v2_struct_0(X16)|~m1_pre_topc(X16,X14))))&(m1_pre_topc(k2_tsep_1(X14,X15,X16),X14)|(v2_struct_0(X14)|~l1_pre_topc(X14)|v2_struct_0(X15)|~m1_pre_topc(X15,X14)|v2_struct_0(X16)|~m1_pre_topc(X16,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X4)&m1_pre_topc(X3,X4))=>(r1_tsep_1(X2,X3)|m1_pre_topc(k2_tsep_1(X1,X2,X3),X4)))))))), inference(assume_negation,[status(cth)],[t30_tmap_1])).
% 0.19/0.37  cnf(c_0_9, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_10, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_11, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((m1_pre_topc(esk2_0,esk4_0)&m1_pre_topc(esk3_0,esk4_0))&(~r1_tsep_1(esk2_0,esk3_0)&~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X17, X18, X19]:((~r1_tarski(u1_struct_0(X18),u1_struct_0(X19))|m1_pre_topc(X18,X19)|~m1_pre_topc(X19,X17)|~m1_pre_topc(X18,X17)|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~m1_pre_topc(X18,X19)|r1_tarski(u1_struct_0(X18),u1_struct_0(X19))|~m1_pre_topc(X19,X17)|~m1_pre_topc(X18,X17)|(~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.19/0.37  cnf(c_0_15, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_20, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))=k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18]), c_0_19])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_27, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_17])])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))=k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.37  fof(c_0_31, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_22]), c_0_17])])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)|~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.37  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25])])).
% 0.19/0.37  fof(c_0_37, plain, ![X5, X6]:r1_tarski(k3_xboole_0(X5,X6),X5), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_10]), c_0_16]), c_0_25]), c_0_17])]), c_0_19]), c_0_26]), c_0_18])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.37  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 42
% 0.19/0.37  # Proof object clause steps            : 29
% 0.19/0.37  # Proof object formula steps           : 13
% 0.19/0.37  # Proof object conjectures             : 23
% 0.19/0.37  # Proof object clause conjectures      : 20
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 19
% 0.19/0.37  # Proof object initial formulas used   : 6
% 0.19/0.37  # Proof object generating inferences   : 9
% 0.19/0.37  # Proof object simplifying inferences  : 29
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 6
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 22
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 22
% 0.19/0.37  # Processed clauses                    : 78
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 78
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 65
% 0.19/0.37  # ...of the previous two non-trivial   : 57
% 0.19/0.37  # Contextual simplify-reflections      : 3
% 0.19/0.37  # Paramodulations                      : 64
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 55
% 0.19/0.37  #    Positive orientable unit clauses  : 12
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 7
% 0.19/0.37  #    Non-unit-clauses                  : 36
% 0.19/0.37  # Current number of unprocessed clauses: 23
% 0.19/0.37  # ...number of literals in the above   : 196
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 22
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 493
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 55
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.37  # Unit Clause-clause subsumption calls : 31
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 4004
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.037 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

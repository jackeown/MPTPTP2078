%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:09 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 121 expanded)
%              Number of clauses        :   27 (  39 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  209 (1154 expanded)
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

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(c_0_5,plain,(
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

fof(c_0_6,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v2_struct_0(k2_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( v1_pre_topc(k2_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( m1_pre_topc(k2_tsep_1(X12,X13,X14),X12)
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

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
                   => ( ( m1_pre_topc(X2,X4)
                        & m1_pre_topc(X3,X4) )
                     => ( r1_tsep_1(X2,X3)
                        | m1_pre_topc(k2_tsep_1(X1,X2,X3),X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_tmap_1])).

cnf(c_0_8,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_tarski(u1_struct_0(X16),u1_struct_0(X17))
        | m1_pre_topc(X16,X17)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_pre_topc(X16,X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_pre_topc(X16,X17)
        | r1_tarski(u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_pre_topc(X16,X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_14,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) = k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | r1_tarski(k3_xboole_0(X5,X7),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_9]),c_0_15]),c_0_24]),c_0_16])]),c_0_18]),c_0_25]),c_0_17])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.21/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.042 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.21/0.40  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.21/0.40  fof(t30_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X4)&m1_pre_topc(X3,X4))=>(r1_tsep_1(X2,X3)|m1_pre_topc(k2_tsep_1(X1,X2,X3),X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 0.21/0.40  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.21/0.40  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.21/0.40  fof(c_0_5, plain, ![X8, X9, X10, X11]:((X11!=k2_tsep_1(X8,X9,X10)|u1_struct_0(X11)=k3_xboole_0(u1_struct_0(X9),u1_struct_0(X10))|(v2_struct_0(X11)|~v1_pre_topc(X11)|~m1_pre_topc(X11,X8))|r1_tsep_1(X9,X10)|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~l1_pre_topc(X8)))&(u1_struct_0(X11)!=k3_xboole_0(u1_struct_0(X9),u1_struct_0(X10))|X11=k2_tsep_1(X8,X9,X10)|(v2_struct_0(X11)|~v1_pre_topc(X11)|~m1_pre_topc(X11,X8))|r1_tsep_1(X9,X10)|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~l1_pre_topc(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.21/0.40  fof(c_0_6, plain, ![X12, X13, X14]:(((~v2_struct_0(k2_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))&(v1_pre_topc(k2_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12))))&(m1_pre_topc(k2_tsep_1(X12,X13,X14),X12)|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.21/0.40  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>((m1_pre_topc(X2,X4)&m1_pre_topc(X3,X4))=>(r1_tsep_1(X2,X3)|m1_pre_topc(k2_tsep_1(X1,X2,X3),X4)))))))), inference(assume_negation,[status(cth)],[t30_tmap_1])).
% 0.21/0.40  cnf(c_0_8, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  cnf(c_0_9, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_10, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_11, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((m1_pre_topc(esk2_0,esk4_0)&m1_pre_topc(esk3_0,esk4_0))&(~r1_tsep_1(esk2_0,esk3_0)&~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.21/0.40  fof(c_0_13, plain, ![X15, X16, X17]:((~r1_tarski(u1_struct_0(X16),u1_struct_0(X17))|m1_pre_topc(X16,X17)|~m1_pre_topc(X17,X15)|~m1_pre_topc(X16,X15)|(~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~m1_pre_topc(X16,X17)|r1_tarski(u1_struct_0(X16),u1_struct_0(X17))|~m1_pre_topc(X17,X15)|~m1_pre_topc(X16,X15)|(~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.21/0.40  cnf(c_0_14, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.21/0.40  cnf(c_0_15, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_19, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))=k3_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])]), c_0_17]), c_0_18])).
% 0.21/0.40  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_16])])).
% 0.21/0.40  cnf(c_0_28, negated_conjecture, (u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))=k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25])).
% 0.21/0.40  cnf(c_0_29, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)|~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.21/0.40  fof(c_0_31, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|r1_tarski(k3_xboole_0(X5,X7),X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_20]), c_0_21]), c_0_16])])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (~r1_tarski(k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_9]), c_0_15]), c_0_24]), c_0_16])]), c_0_18]), c_0_25]), c_0_17])).
% 0.21/0.40  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24])])).
% 0.21/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 38
% 0.21/0.40  # Proof object clause steps            : 27
% 0.21/0.40  # Proof object formula steps           : 11
% 0.21/0.40  # Proof object conjectures             : 22
% 0.21/0.40  # Proof object clause conjectures      : 19
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 18
% 0.21/0.40  # Proof object initial formulas used   : 5
% 0.21/0.40  # Proof object generating inferences   : 8
% 0.21/0.40  # Proof object simplifying inferences  : 29
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 5
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 21
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 21
% 0.21/0.40  # Processed clauses                    : 64
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 0
% 0.21/0.40  # ...remaining for further processing  : 64
% 0.21/0.40  # Other redundant clauses eliminated   : 1
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 0
% 0.21/0.40  # Generated clauses                    : 50
% 0.21/0.40  # ...of the previous two non-trivial   : 45
% 0.21/0.40  # Contextual simplify-reflections      : 3
% 0.21/0.40  # Paramodulations                      : 49
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 1
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 42
% 0.21/0.40  #    Positive orientable unit clauses  : 10
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 7
% 0.21/0.40  #    Non-unit-clauses                  : 25
% 0.21/0.40  # Current number of unprocessed clauses: 23
% 0.21/0.40  # ...number of literals in the above   : 210
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 21
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 290
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 39
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 3
% 0.21/0.40  # Unit Clause-clause subsumption calls : 13
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 0
% 0.21/0.40  # BW rewrite match successes           : 0
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 3435
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.050 s
% 0.21/0.40  # System time              : 0.003 s
% 0.21/0.40  # Total time               : 0.053 s
% 0.21/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

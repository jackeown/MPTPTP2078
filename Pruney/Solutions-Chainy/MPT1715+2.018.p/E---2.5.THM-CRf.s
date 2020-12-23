%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 397 expanded)
%              Number of clauses        :   31 ( 152 expanded)
%              Number of leaves         :    7 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 (2630 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_tmap_1,conjecture,(
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

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

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

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

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
                     => ( ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X4,X3) )
                        | ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_tmap_1])).

fof(c_0_8,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
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
    & ( r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(esk4_0,esk3_0) )
    & ( ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk4_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | l1_struct_0(X8) ) ),
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
    ! [X13,X14] :
      ( ~ l1_struct_0(X13)
      | ~ l1_struct_0(X14)
      | ~ r1_tsep_1(X13,X14)
      | r1_tsep_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_16,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_13])])).

cnf(c_0_19,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

fof(c_0_23,plain,(
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

cnf(c_0_24,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_22]),c_0_21])])).

cnf(c_0_29,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21]),c_0_22])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_30]),c_0_13])])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_34]),c_0_13])])).

cnf(c_0_39,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21]),c_0_41])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_43]),c_0_21]),c_0_41])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03AI
% 0.14/0.37  # and selection function SelectComplex.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t24_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 0.14/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.14/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.37  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.14/0.37  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.14/0.37  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.14/0.37  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.14/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))))))))), inference(assume_negation,[status(cth)],[t24_tmap_1])).
% 0.14/0.37  fof(c_0_8, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.14/0.37  fof(c_0_9, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(m1_pre_topc(esk2_0,esk3_0)&((r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0))&(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.14/0.37  fof(c_0_10, plain, ![X8]:(~l1_pre_topc(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.37  cnf(c_0_11, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_12, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  fof(c_0_15, plain, ![X13, X14]:(~l1_struct_0(X13)|~l1_struct_0(X14)|(~r1_tsep_1(X13,X14)|r1_tsep_1(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.14/0.37  cnf(c_0_16, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_14]), c_0_13])])).
% 0.14/0.37  cnf(c_0_19, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_18])).
% 0.14/0.37  fof(c_0_23, plain, ![X11, X12]:((~r1_tsep_1(X11,X12)|r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|~l1_struct_0(X12)|~l1_struct_0(X11))&(~r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|r1_tsep_1(X11,X12)|~l1_struct_0(X12)|~l1_struct_0(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.14/0.37  fof(c_0_25, plain, ![X15, X16, X17]:((~r1_tarski(u1_struct_0(X16),u1_struct_0(X17))|m1_pre_topc(X16,X17)|~m1_pre_topc(X17,X15)|~m1_pre_topc(X16,X15)|(~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~m1_pre_topc(X16,X17)|r1_tarski(u1_struct_0(X16),u1_struct_0(X17))|~m1_pre_topc(X17,X15)|~m1_pre_topc(X16,X15)|(~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.14/0.37  fof(c_0_26, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_xboole_0(X6,X7)|r1_xboole_0(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.14/0.37  cnf(c_0_27, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_22]), c_0_21])])).
% 0.14/0.37  cnf(c_0_29, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_31, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21]), c_0_22])])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_14]), c_0_30]), c_0_13])])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_34]), c_0_13])])).
% 0.14/0.37  cnf(c_0_39, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.37  cnf(c_0_41, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_38])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_21]), c_0_41])])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (~r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_43]), c_0_21]), c_0_41])]), c_0_44]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 46
% 0.14/0.37  # Proof object clause steps            : 31
% 0.14/0.37  # Proof object formula steps           : 15
% 0.14/0.37  # Proof object conjectures             : 27
% 0.14/0.37  # Proof object clause conjectures      : 24
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 15
% 0.14/0.37  # Proof object initial formulas used   : 7
% 0.14/0.37  # Proof object generating inferences   : 15
% 0.14/0.37  # Proof object simplifying inferences  : 29
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 7
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 20
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 20
% 0.14/0.37  # Processed clauses                    : 70
% 0.14/0.37  # ...of these trivial                  : 1
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 68
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 2
% 0.14/0.37  # Generated clauses                    : 37
% 0.14/0.37  # ...of the previous two non-trivial   : 33
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 37
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 46
% 0.14/0.37  #    Positive orientable unit clauses  : 20
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 5
% 0.14/0.37  #    Non-unit-clauses                  : 21
% 0.14/0.37  # Current number of unprocessed clauses: 2
% 0.14/0.37  # ...number of literals in the above   : 4
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 22
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 75
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 12
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 24
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 2
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1974
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.030 s
% 0.14/0.37  # System time              : 0.003 s
% 0.14/0.37  # Total time               : 0.033 s
% 0.14/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

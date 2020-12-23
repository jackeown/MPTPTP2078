%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 120 expanded)
%              Number of clauses        :   33 (  54 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 ( 342 expanded)
%              Number of equality atoms :   24 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t2_yellow19,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(t11_waybel_7,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
     => ( v13_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3,X4] :
            ( ( r1_tarski(X3,X4)
              & r1_tarski(X4,X1)
              & r2_hidden(X3,X2) )
           => r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_11,plain,(
    ! [X24] : k3_yellow_1(X24) = k2_yellow_1(k9_setfam_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_12,plain,(
    ! [X22] : k9_setfam_1(X22) = k1_zfmisc_1(X22) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
              & v2_waybel_0(X2,k3_yellow_1(X1))
              & v13_waybel_0(X2,k3_yellow_1(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
           => ! [X3] :
                ~ ( r2_hidden(X3,X2)
                  & v1_xboole_0(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_yellow19])).

fof(c_0_14,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ r1_tarski(X27,X28)
        | ~ r1_tarski(X28,X25)
        | ~ r2_hidden(X27,X26)
        | r2_hidden(X28,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( r1_tarski(esk4_2(X25,X26),esk5_2(X25,X26))
        | v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( r1_tarski(esk5_2(X25,X26),X25)
        | v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( r2_hidden(esk4_2(X25,X26),X26)
        | v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( ~ r2_hidden(esk5_2(X25,X26),X26)
        | v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).

cnf(c_0_15,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0)))
    & v2_waybel_0(esk7_0,k3_yellow_1(esk6_0))
    & v13_waybel_0(esk7_0,k3_yellow_1(esk6_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0))))
    & r2_hidden(esk8_0,esk7_0)
    & v1_xboole_0(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X23] :
      ( u1_struct_0(k2_yellow_1(X23)) = X23
      & u1_orders_2(k2_yellow_1(X23)) = k1_yellow_1(X23) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X4,X1)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ v13_waybel_0(X1,k2_yellow_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_23,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0))))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_26,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X16,X17] :
      ( ( m1_subset_1(esk3_2(X16,X17),X16)
        | X16 = X17
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) )
      & ( ~ r2_hidden(esk3_2(X16,X17),X17)
        | X16 = X17
        | ~ m1_subset_1(X17,k1_zfmisc_1(X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

fof(c_0_28,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,k2_yellow_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X4,X1)
    | ~ r2_hidden(X4,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v13_waybel_0(esk7_0,k2_yellow_1(k1_zfmisc_1(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk3_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_38,plain,
    ( k1_zfmisc_1(X1) = X2
    | r1_tarski(esk3_2(k1_zfmisc_1(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( k1_zfmisc_1(esk6_0) = X1
    | r2_hidden(esk3_2(k1_zfmisc_1(esk6_0),X1),esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))
    | ~ r1_tarski(X2,esk3_2(k1_zfmisc_1(esk6_0),X1))
    | ~ r2_hidden(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_45,plain,(
    ! [X19] : ~ v1_subset_1(k2_subset_1(X19),X19) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_46,plain,(
    ! [X15] : k2_subset_1(X15) = X15 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_47,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_19])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( k1_zfmisc_1(esk6_0) = X1
    | r2_hidden(esk3_2(k1_zfmisc_1(esk6_0),X1),esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_50,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_subset_1(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( k1_zfmisc_1(esk6_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_32])])).

cnf(c_0_54,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:29:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.035 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.20/0.40  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.20/0.40  fof(t2_yellow19, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 0.20/0.40  fof(t11_waybel_7, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))=>(v13_waybel_0(X2,k3_yellow_1(X1))<=>![X3, X4]:(((r1_tarski(X3,X4)&r1_tarski(X4,X1))&r2_hidden(X3,X2))=>r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_waybel_7)).
% 0.20/0.40  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.40  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.40  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.20/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.40  fof(c_0_11, plain, ![X24]:k3_yellow_1(X24)=k2_yellow_1(k9_setfam_1(X24)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.20/0.40  fof(c_0_12, plain, ![X22]:k9_setfam_1(X22)=k1_zfmisc_1(X22), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.20/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3)))))), inference(assume_negation,[status(cth)],[t2_yellow19])).
% 0.20/0.40  fof(c_0_14, plain, ![X25, X26, X27, X28]:((~v13_waybel_0(X26,k3_yellow_1(X25))|(~r1_tarski(X27,X28)|~r1_tarski(X28,X25)|~r2_hidden(X27,X26)|r2_hidden(X28,X26))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))))&((((r1_tarski(esk4_2(X25,X26),esk5_2(X25,X26))|v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))))&(r1_tarski(esk5_2(X25,X26),X25)|v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))&(r2_hidden(esk4_2(X25,X26),X26)|v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))&(~r2_hidden(esk5_2(X25,X26),X26)|v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).
% 0.20/0.40  cnf(c_0_15, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_16, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk6_0)&(((((~v1_xboole_0(esk7_0)&v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0))))&v2_waybel_0(esk7_0,k3_yellow_1(esk6_0)))&v13_waybel_0(esk7_0,k3_yellow_1(esk6_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0)))))&(r2_hidden(esk8_0,esk7_0)&v1_xboole_0(esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.20/0.40  cnf(c_0_18, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,k3_yellow_1(X2))|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_19, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  fof(c_0_20, plain, ![X23]:(u1_struct_0(k2_yellow_1(X23))=X23&u1_orders_2(k2_yellow_1(X23))=k1_yellow_1(X23)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_22, plain, (r2_hidden(X4,X1)|~r2_hidden(X3,X1)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)|~v13_waybel_0(X1,k2_yellow_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.20/0.40  cnf(c_0_23, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (v13_waybel_0(esk7_0,k3_yellow_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0)))))), inference(rw,[status(thm)],[c_0_21, c_0_19])).
% 0.20/0.40  fof(c_0_26, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.40  fof(c_0_27, plain, ![X16, X17]:((m1_subset_1(esk3_2(X16,X17),X16)|X16=X17|~m1_subset_1(X17,k1_zfmisc_1(X16)))&(~r2_hidden(esk3_2(X16,X17),X17)|X16=X17|~m1_subset_1(X17,k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.20/0.40  fof(c_0_28, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  fof(c_0_29, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.40  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,k2_yellow_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~r1_tarski(X1,X3)|~r1_tarski(X4,X1)|~r2_hidden(X4,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (v13_waybel_0(esk7_0,k2_yellow_1(k1_zfmisc_1(esk6_0)))), inference(rw,[status(thm)],[c_0_24, c_0_19])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))), inference(rw,[status(thm)],[c_0_25, c_0_23])).
% 0.20/0.40  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_34, plain, (m1_subset_1(esk3_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_36, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk7_0)|~r1_tarski(X1,esk6_0)|~r1_tarski(X2,X1)|~r2_hidden(X2,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.20/0.40  cnf(c_0_38, plain, (k1_zfmisc_1(X1)=X2|r1_tarski(esk3_2(k1_zfmisc_1(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.40  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (k1_zfmisc_1(esk6_0)=X1|r2_hidden(esk3_2(k1_zfmisc_1(esk6_0),X1),esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))|~r1_tarski(X2,esk3_2(k1_zfmisc_1(esk6_0),X1))|~r2_hidden(X2,esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_45, plain, ![X19]:~v1_subset_1(k2_subset_1(X19),X19), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.20/0.40  fof(c_0_46, plain, ![X15]:k2_subset_1(X15)=X15, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0))))), inference(rw,[status(thm)],[c_0_41, c_0_19])).
% 0.20/0.40  cnf(c_0_48, plain, (X1=X2|~r2_hidden(esk3_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (k1_zfmisc_1(esk6_0)=X1|r2_hidden(esk3_2(k1_zfmisc_1(esk6_0),X1),esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.20/0.40  cnf(c_0_50, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.40  cnf(c_0_51, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (v1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))), inference(rw,[status(thm)],[c_0_47, c_0_23])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (k1_zfmisc_1(esk6_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_32])])).
% 0.20/0.40  cnf(c_0_54, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 56
% 0.20/0.40  # Proof object clause steps            : 33
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 19
% 0.20/0.40  # Proof object clause conjectures      : 16
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 16
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 7
% 0.20/0.40  # Proof object simplifying inferences  : 18
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 28
% 0.20/0.40  # Removed in clause preprocessing      : 4
% 0.20/0.40  # Initial clauses in saturation        : 24
% 0.20/0.40  # Processed clauses                    : 114
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 12
% 0.20/0.40  # ...remaining for further processing  : 102
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 13
% 0.20/0.40  # Backward-rewritten                   : 19
% 0.20/0.40  # Generated clauses                    : 254
% 0.20/0.40  # ...of the previous two non-trivial   : 220
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 254
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 70
% 0.20/0.40  #    Positive orientable unit clauses  : 7
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 4
% 0.20/0.40  #    Non-unit-clauses                  : 59
% 0.20/0.40  # Current number of unprocessed clauses: 114
% 0.20/0.40  # ...number of literals in the above   : 563
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 36
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1085
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 484
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 22
% 0.20/0.40  # Unit Clause-clause subsumption calls : 25
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 8
% 0.20/0.40  # BW rewrite match successes           : 2
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 7882
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.057 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.061 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

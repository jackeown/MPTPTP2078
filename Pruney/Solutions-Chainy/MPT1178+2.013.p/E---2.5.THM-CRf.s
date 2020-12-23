%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:13 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 198 expanded)
%              Number of clauses        :   29 (  72 expanded)
%              Number of leaves         :    9 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 ( 896 expanded)
%              Number of equality atoms :   17 ( 109 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc9_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k4_orders_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(t79_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | r1_tarski(X12,k3_tarski(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_10,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0)))
    & k3_tarski(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_16,plain,
    ( r1_tarski(esk1_1(X1),k3_tarski(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_1(k4_orders_2(esk3_0,esk4_0)),k1_xboole_0)
    | v1_xboole_0(k4_orders_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v3_orders_2(X21)
      | ~ v4_orders_2(X21)
      | ~ v5_orders_2(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(X21)))
      | ~ v1_xboole_0(k4_orders_2(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_23,negated_conjecture,
    ( esk1_1(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0
    | v1_xboole_0(k4_orders_2(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_24,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X16)
        | m2_orders_2(X17,X14,X15)
        | X16 != k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ m2_orders_2(X18,X14,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X19),X19)
        | ~ m2_orders_2(esk2_3(X14,X15,X19),X14,X15)
        | X19 = k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X19),X19)
        | m2_orders_2(esk2_3(X14,X15,X19),X14,X15)
        | X19 = k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k4_orders_2(esk3_0,esk4_0))
    | v1_xboole_0(k4_orders_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k4_orders_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

fof(c_0_36,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v3_orders_2(X23)
      | ~ v4_orders_2(X23)
      | ~ v5_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))
      | ~ m2_orders_2(X25,X23,X24)
      | r2_hidden(k1_funct_1(X24,u1_struct_0(X23)),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

cnf(c_0_37,plain,
    ( m2_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,k4_orders_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(k4_orders_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( m2_orders_2(X1,esk3_0,esk4_0)
    | ~ r2_hidden(X1,k4_orders_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( esk1_1(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_23,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),X1)
    | ~ m2_orders_2(X1,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( m2_orders_2(k1_xboole_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_13]),c_0_41]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:18:38 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.11/0.36  # and selection function SelectNewComplexAHPNS.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.028 s
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.11/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.11/0.36  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.11/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.11/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.11/0.36  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 0.11/0.36  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.11/0.36  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 0.11/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.11/0.36  fof(c_0_9, plain, ![X12, X13]:(~r2_hidden(X12,X13)|r1_tarski(X12,k3_tarski(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.11/0.36  fof(c_0_10, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.11/0.36  fof(c_0_11, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.11/0.36  cnf(c_0_12, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.36  cnf(c_0_13, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0)))&k3_tarski(k4_orders_2(esk3_0,esk4_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.11/0.36  fof(c_0_15, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.11/0.36  cnf(c_0_16, plain, (r1_tarski(esk1_1(X1),k3_tarski(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.11/0.36  cnf(c_0_17, negated_conjecture, (k3_tarski(k4_orders_2(esk3_0,esk4_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  fof(c_0_18, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.11/0.36  cnf(c_0_19, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.36  cnf(c_0_20, negated_conjecture, (r1_tarski(esk1_1(k4_orders_2(esk3_0,esk4_0)),k1_xboole_0)|v1_xboole_0(k4_orders_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.36  cnf(c_0_21, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.36  fof(c_0_22, plain, ![X21, X22]:(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_orders_1(X22,k1_orders_1(u1_struct_0(X21)))|~v1_xboole_0(k4_orders_2(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 0.11/0.36  cnf(c_0_23, negated_conjecture, (esk1_1(k4_orders_2(esk3_0,esk4_0))=k1_xboole_0|v1_xboole_0(k4_orders_2(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.11/0.36  fof(c_0_24, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X17,X16)|m2_orders_2(X17,X14,X15)|X16!=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)))&(~m2_orders_2(X18,X14,X15)|r2_hidden(X18,X16)|X16!=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))&((~r2_hidden(esk2_3(X14,X15,X19),X19)|~m2_orders_2(esk2_3(X14,X15,X19),X14,X15)|X19=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)))&(r2_hidden(esk2_3(X14,X15,X19),X19)|m2_orders_2(esk2_3(X14,X15,X19),X14,X15)|X19=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.11/0.36  cnf(c_0_25, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.36  cnf(c_0_26, negated_conjecture, (r2_hidden(k1_xboole_0,k4_orders_2(esk3_0,esk4_0))|v1_xboole_0(k4_orders_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_23])).
% 0.11/0.36  cnf(c_0_27, negated_conjecture, (m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_28, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_29, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_30, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_31, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  cnf(c_0_33, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.36  cnf(c_0_34, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_xboole_0,k4_orders_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.11/0.36  fof(c_0_36, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|(~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))|(~m2_orders_2(X25,X23,X24)|r2_hidden(k1_funct_1(X24,u1_struct_0(X23)),X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.11/0.36  cnf(c_0_37, plain, (m2_orders_2(X1,X2,X3)|v2_struct_0(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,k4_orders_2(X2,X3))), inference(er,[status(thm)],[c_0_33])).
% 0.11/0.36  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(k4_orders_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.11/0.36  cnf(c_0_39, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.11/0.36  cnf(c_0_40, negated_conjecture, (m2_orders_2(X1,esk3_0,esk4_0)|~r2_hidden(X1,k4_orders_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.11/0.36  cnf(c_0_41, negated_conjecture, (esk1_1(k4_orders_2(esk3_0,esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[c_0_23, c_0_38])).
% 0.11/0.36  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),X1)|~m2_orders_2(X1,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.11/0.36  cnf(c_0_43, negated_conjecture, (m2_orders_2(k1_xboole_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_13]), c_0_41]), c_0_38])).
% 0.11/0.36  cnf(c_0_44, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.11/0.36  cnf(c_0_45, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.11/0.36  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_44]), c_0_45])]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 47
% 0.11/0.36  # Proof object clause steps            : 29
% 0.11/0.36  # Proof object formula steps           : 18
% 0.11/0.36  # Proof object conjectures             : 21
% 0.11/0.36  # Proof object clause conjectures      : 18
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 16
% 0.11/0.36  # Proof object initial formulas used   : 9
% 0.11/0.36  # Proof object generating inferences   : 11
% 0.11/0.36  # Proof object simplifying inferences  : 27
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 9
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 21
% 0.11/0.36  # Removed in clause preprocessing      : 0
% 0.11/0.36  # Initial clauses in saturation        : 21
% 0.11/0.36  # Processed clauses                    : 48
% 0.11/0.36  # ...of these trivial                  : 3
% 0.11/0.36  # ...subsumed                          : 2
% 0.11/0.36  # ...remaining for further processing  : 43
% 0.11/0.36  # Other redundant clauses eliminated   : 4
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 1
% 0.11/0.36  # Generated clauses                    : 46
% 0.11/0.36  # ...of the previous two non-trivial   : 34
% 0.11/0.36  # Contextual simplify-reflections      : 0
% 0.11/0.36  # Paramodulations                      : 40
% 0.11/0.36  # Factorizations                       : 0
% 0.11/0.36  # Equation resolutions                 : 4
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 36
% 0.11/0.36  #    Positive orientable unit clauses  : 13
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 2
% 0.11/0.36  #    Non-unit-clauses                  : 21
% 0.11/0.36  # Current number of unprocessed clauses: 7
% 0.11/0.36  # ...number of literals in the above   : 21
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 3
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 89
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 40
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.11/0.36  # Unit Clause-clause subsumption calls : 15
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 5
% 0.11/0.36  # BW rewrite match successes           : 1
% 0.11/0.36  # Condensation attempts                : 48
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 2522
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.030 s
% 0.11/0.36  # System time              : 0.004 s
% 0.11/0.36  # Total time               : 0.034 s
% 0.11/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:39 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 518 expanded)
%              Number of clauses        :   47 ( 237 expanded)
%              Number of leaves         :   14 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 (1394 expanded)
%              Number of equality atoms :   33 ( 310 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(fc8_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_14,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_15,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( ( ~ r1_xboole_0(X24,X25)
        | k4_xboole_0(X24,X25) = X24 )
      & ( k4_xboole_0(X24,X25) != X24
        | r1_xboole_0(X24,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_20,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

fof(c_0_26,plain,(
    ! [X28] :
      ( v1_xboole_0(X28)
      | ~ v1_relat_1(X28)
      | ~ v1_xboole_0(k1_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k7_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_30,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) )
    & ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_34,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(k1_relat_1(X1),k1_relat_1(X1)),k1_relat_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1)))
    | v1_xboole_0(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,X30)
        | ~ r2_hidden(X29,k1_relat_1(k7_relat_1(X31,X30)))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(X29,k1_relat_1(X31))
        | ~ r2_hidden(X29,k1_relat_1(k7_relat_1(X31,X30)))
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(X29,X30)
        | ~ r2_hidden(X29,k1_relat_1(X31))
        | r2_hidden(X29,k1_relat_1(k7_relat_1(X31,X30)))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)
    | k7_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0)))
    | r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))
    | k7_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_45])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)
    | r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_35])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0)))
    | r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)
    | ~ r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X1)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(esk4_0))
    | r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_47]),c_0_35])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)
    | r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_52]),c_0_35])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))
    | ~ r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X1)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(esk4_0))
    | r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_35])])).

fof(c_0_59,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),X1)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_45])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_63,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_17])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(k7_relat_1(esk4_0,X1)))
    | ~ r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_61]),c_0_35])])).

cnf(c_0_70,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_22]),c_0_27]),c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_56]),c_0_70]),c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:18:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 2.44/2.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 2.44/2.66  # and selection function SelectLargestOrientable.
% 2.44/2.66  #
% 2.44/2.66  # Preprocessing time       : 0.032 s
% 2.44/2.66  # Presaturation interreduction done
% 2.44/2.66  
% 2.44/2.66  # Proof found!
% 2.44/2.66  # SZS status Theorem
% 2.44/2.66  # SZS output start CNFRefutation
% 2.44/2.66  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.44/2.66  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.44/2.66  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.44/2.66  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.44/2.66  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.44/2.66  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.44/2.66  fof(fc8_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.44/2.66  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.44/2.66  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.44/2.66  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.44/2.66  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.44/2.66  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.44/2.66  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.44/2.66  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.44/2.66  fof(c_0_14, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 2.44/2.66  fof(c_0_15, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.44/2.66  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.44/2.66  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.44/2.66  fof(c_0_18, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.44/2.66  fof(c_0_19, plain, ![X24, X25]:((~r1_xboole_0(X24,X25)|k4_xboole_0(X24,X25)=X24)&(k4_xboole_0(X24,X25)!=X24|r1_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 2.44/2.66  fof(c_0_20, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 2.44/2.66  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 2.44/2.66  cnf(c_0_22, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.44/2.66  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.44/2.66  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.44/2.66  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 2.44/2.66  fof(c_0_26, plain, ![X28]:(v1_xboole_0(X28)|~v1_relat_1(X28)|~v1_xboole_0(k1_relat_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).
% 2.44/2.66  cnf(c_0_27, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 2.44/2.66  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.44/2.66  fof(c_0_29, plain, ![X26, X27]:(~v1_relat_1(X26)|v1_relat_1(k7_relat_1(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 2.44/2.66  fof(c_0_30, negated_conjecture, (v1_relat_1(esk4_0)&((k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0))&(k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 2.44/2.66  cnf(c_0_31, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.44/2.66  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.44/2.66  cnf(c_0_33, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 2.44/2.66  cnf(c_0_34, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.44/2.66  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.44/2.66  fof(c_0_36, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 2.44/2.66  cnf(c_0_37, plain, (r2_hidden(esk1_2(k1_relat_1(X1),k1_relat_1(X1)),k1_relat_1(X1))|v1_xboole_0(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 2.44/2.66  cnf(c_0_38, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.44/2.66  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.44/2.66  cnf(c_0_40, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.44/2.66  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1)))|v1_xboole_0(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.44/2.66  fof(c_0_42, plain, ![X29, X30, X31]:(((r2_hidden(X29,X30)|~r2_hidden(X29,k1_relat_1(k7_relat_1(X31,X30)))|~v1_relat_1(X31))&(r2_hidden(X29,k1_relat_1(X31))|~r2_hidden(X29,k1_relat_1(k7_relat_1(X31,X30)))|~v1_relat_1(X31)))&(~r2_hidden(X29,X30)|~r2_hidden(X29,k1_relat_1(X31))|r2_hidden(X29,k1_relat_1(k7_relat_1(X31,X30)))|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 2.44/2.66  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)|k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 2.44/2.66  cnf(c_0_44, negated_conjecture, (k7_relat_1(esk4_0,X1)=k1_xboole_0|r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.44/2.66  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.44/2.66  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.44/2.66  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0)))|r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.44/2.66  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))|k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_45])).
% 2.44/2.66  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.44/2.66  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)|r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_35])])).
% 2.44/2.66  cnf(c_0_51, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.44/2.66  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(k7_relat_1(esk4_0,esk3_0)))|r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_44])).
% 2.44/2.66  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)|~r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X1)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.44/2.66  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(esk4_0))|r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_47]), c_0_35])])).
% 2.44/2.66  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),esk3_0)|r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_52]), c_0_35])])).
% 2.44/2.66  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_24])).
% 2.44/2.66  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))|~r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),X1)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_55])).
% 2.44/2.66  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_relat_1(k7_relat_1(esk4_0,esk3_0))),k1_relat_1(esk4_0))|r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_35])])).
% 2.44/2.66  fof(c_0_59, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 2.44/2.66  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),X1)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_56])).
% 2.44/2.66  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_45])).
% 2.44/2.66  cnf(c_0_62, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.44/2.66  fof(c_0_63, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 2.44/2.66  cnf(c_0_64, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.44/2.66  cnf(c_0_65, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.44/2.66  cnf(c_0_66, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 2.44/2.66  cnf(c_0_67, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_62, c_0_17])).
% 2.44/2.66  cnf(c_0_68, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.44/2.66  cnf(c_0_69, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),k1_relat_1(k7_relat_1(esk4_0,X1)))|~r2_hidden(esk1_2(k1_relat_1(esk4_0),esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_61]), c_0_35])])).
% 2.44/2.66  cnf(c_0_70, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_65, c_0_66])).
% 2.44/2.66  cnf(c_0_71, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 2.44/2.66  cnf(c_0_72, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_22]), c_0_27]), c_0_68])])).
% 2.44/2.66  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_56]), c_0_70]), c_0_71]), c_0_72]), ['proof']).
% 2.44/2.66  # SZS output end CNFRefutation
% 2.44/2.66  # Proof object total steps             : 74
% 2.44/2.66  # Proof object clause steps            : 47
% 2.44/2.66  # Proof object formula steps           : 27
% 2.44/2.66  # Proof object conjectures             : 26
% 2.44/2.66  # Proof object clause conjectures      : 23
% 2.44/2.66  # Proof object formula conjectures     : 3
% 2.44/2.66  # Proof object initial clauses used    : 20
% 2.44/2.66  # Proof object initial formulas used   : 14
% 2.44/2.66  # Proof object generating inferences   : 23
% 2.44/2.66  # Proof object simplifying inferences  : 24
% 2.44/2.66  # Training examples: 0 positive, 0 negative
% 2.44/2.66  # Parsed axioms                        : 15
% 2.44/2.66  # Removed by relevancy pruning/SinE    : 0
% 2.44/2.66  # Initial clauses                      : 24
% 2.44/2.66  # Removed in clause preprocessing      : 1
% 2.44/2.66  # Initial clauses in saturation        : 23
% 2.44/2.66  # Processed clauses                    : 11037
% 2.44/2.66  # ...of these trivial                  : 600
% 2.44/2.66  # ...subsumed                          : 9072
% 2.44/2.66  # ...remaining for further processing  : 1365
% 2.44/2.66  # Other redundant clauses eliminated   : 2001
% 2.44/2.66  # Clauses deleted for lack of memory   : 0
% 2.44/2.66  # Backward-subsumed                    : 220
% 2.44/2.66  # Backward-rewritten                   : 450
% 2.44/2.66  # Generated clauses                    : 342728
% 2.44/2.66  # ...of the previous two non-trivial   : 251742
% 2.44/2.66  # Contextual simplify-reflections      : 24
% 2.44/2.66  # Paramodulations                      : 340694
% 2.44/2.66  # Factorizations                       : 8
% 2.44/2.66  # Equation resolutions                 : 2001
% 2.44/2.66  # Propositional unsat checks           : 0
% 2.44/2.66  #    Propositional check models        : 0
% 2.44/2.66  #    Propositional check unsatisfiable : 0
% 2.44/2.66  #    Propositional clauses             : 0
% 2.44/2.66  #    Propositional clauses after purity: 0
% 2.44/2.66  #    Propositional unsat core size     : 0
% 2.44/2.66  #    Propositional preprocessing time  : 0.000
% 2.44/2.66  #    Propositional encoding time       : 0.000
% 2.44/2.66  #    Propositional solver time         : 0.000
% 2.44/2.66  #    Success case prop preproc time    : 0.000
% 2.44/2.66  #    Success case prop encoding time   : 0.000
% 2.44/2.66  #    Success case prop solver time     : 0.000
% 2.44/2.66  # Current number of processed clauses  : 647
% 2.44/2.66  #    Positive orientable unit clauses  : 118
% 2.44/2.66  #    Positive unorientable unit clauses: 0
% 2.44/2.66  #    Negative unit clauses             : 38
% 2.44/2.66  #    Non-unit-clauses                  : 491
% 2.44/2.66  # Current number of unprocessed clauses: 238440
% 2.44/2.66  # ...number of literals in the above   : 1019837
% 2.44/2.66  # Current number of archived formulas  : 0
% 2.44/2.66  # Current number of archived clauses   : 719
% 2.44/2.66  # Clause-clause subsumption calls (NU) : 282617
% 2.44/2.66  # Rec. Clause-clause subsumption calls : 167875
% 2.44/2.66  # Non-unit clause-clause subsumptions  : 8154
% 2.44/2.66  # Unit Clause-clause subsumption calls : 3476
% 2.44/2.66  # Rewrite failures with RHS unbound    : 0
% 2.44/2.66  # BW rewrite match attempts            : 1746
% 2.44/2.66  # BW rewrite match successes           : 21
% 2.44/2.66  # Condensation attempts                : 0
% 2.44/2.66  # Condensation successes               : 0
% 2.44/2.66  # Termbank termtop insertions          : 8880211
% 2.44/2.67  
% 2.44/2.67  # -------------------------------------------------
% 2.44/2.67  # User time                : 2.236 s
% 2.44/2.67  # System time              : 0.088 s
% 2.44/2.67  # Total time               : 2.324 s
% 2.44/2.67  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

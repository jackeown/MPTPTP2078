%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:14 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 149 expanded)
%              Number of clauses        :   47 (  64 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  269 ( 627 expanded)
%              Number of equality atoms :   53 ( 156 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t72_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(c_0_11,plain,(
    ! [X83,X84,X85] :
      ( ( r2_hidden(X83,k1_relat_1(X85))
        | ~ r2_hidden(X83,k1_relat_1(k5_relat_1(X85,k6_relat_1(X84))))
        | ~ v1_relat_1(X85)
        | ~ v1_funct_1(X85) )
      & ( r2_hidden(k1_funct_1(X85,X83),X84)
        | ~ r2_hidden(X83,k1_relat_1(k5_relat_1(X85,k6_relat_1(X84))))
        | ~ v1_relat_1(X85)
        | ~ v1_funct_1(X85) )
      & ( ~ r2_hidden(X83,k1_relat_1(X85))
        | ~ r2_hidden(k1_funct_1(X85,X83),X84)
        | r2_hidden(X83,k1_relat_1(k5_relat_1(X85,k6_relat_1(X84))))
        | ~ v1_relat_1(X85)
        | ~ v1_funct_1(X85) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).

fof(c_0_12,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X64)
      | k7_relat_1(X64,X63) = k5_relat_1(k6_relat_1(X63),X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_13,plain,(
    ! [X75] :
      ( v1_relat_1(k6_relat_1(X75))
      & v1_funct_1(k6_relat_1(X75)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_14,plain,(
    ! [X65,X66,X67,X69,X70,X71,X73] :
      ( ( r2_hidden(esk4_3(X65,X66,X67),k1_relat_1(X65))
        | ~ r2_hidden(X67,X66)
        | X66 != k2_relat_1(X65)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( X67 = k1_funct_1(X65,esk4_3(X65,X66,X67))
        | ~ r2_hidden(X67,X66)
        | X66 != k2_relat_1(X65)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( ~ r2_hidden(X70,k1_relat_1(X65))
        | X69 != k1_funct_1(X65,X70)
        | r2_hidden(X69,X66)
        | X66 != k2_relat_1(X65)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( ~ r2_hidden(esk5_2(X65,X71),X71)
        | ~ r2_hidden(X73,k1_relat_1(X65))
        | esk5_2(X65,X71) != k1_funct_1(X65,X73)
        | X71 = k2_relat_1(X65)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( r2_hidden(esk6_2(X65,X71),k1_relat_1(X65))
        | r2_hidden(esk5_2(X65,X71),X71)
        | X71 = k2_relat_1(X65)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( esk5_2(X65,X71) = k1_funct_1(X65,esk6_2(X65,X71))
        | r2_hidden(esk5_2(X65,X71),X71)
        | X71 = k2_relat_1(X65)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_15,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X60,X61,X62] :
      ( ( r2_hidden(X60,X61)
        | ~ r2_hidden(X60,k1_relat_1(k7_relat_1(X62,X61)))
        | ~ v1_relat_1(X62) )
      & ( r2_hidden(X60,k1_relat_1(X62))
        | ~ r2_hidden(X60,k1_relat_1(k7_relat_1(X62,X61)))
        | ~ v1_relat_1(X62) )
      & ( ~ r2_hidden(X60,X61)
        | ~ r2_hidden(X60,k1_relat_1(X62))
        | r2_hidden(X60,k1_relat_1(k7_relat_1(X62,X61)))
        | ~ v1_relat_1(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_21,plain,(
    ! [X59] :
      ( k1_relat_1(k6_relat_1(X59)) = X59
      & k2_relat_1(k6_relat_1(X59)) = X59 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X76,X77,X79] :
      ( v1_relat_1(esk7_2(X76,X77))
      & v1_funct_1(esk7_2(X76,X77))
      & k1_relat_1(esk7_2(X76,X77)) = X76
      & ( ~ r2_hidden(X79,X76)
        | k1_funct_1(esk7_2(X76,X77),X79) = X77 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,X2)
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t72_funct_1])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_19])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

cnf(c_0_30,plain,
    ( k1_funct_1(esk7_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_funct_1(esk7_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v1_relat_1(esk7_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k1_relat_1(esk7_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & r2_hidden(esk8_0,esk9_0)
    & k1_funct_1(k7_relat_1(esk10_0,esk9_0),esk8_0) != k1_funct_1(esk10_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X3)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19]),c_0_28])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_relat_1(esk7_2(X2,X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X3)
    | ~ r2_hidden(X2,k4_xboole_0(X4,X3))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk7_2(esk9_0,X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(esk9_0,X1))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_44,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_45,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(X3),X1)))))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk8_0,k4_xboole_0(k4_xboole_0(esk9_0,X1),X2))
    | r2_hidden(esk8_0,X1)
    | r2_hidden(esk8_0,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43])).

cnf(c_0_49,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(X1),esk8_0))))
    | r2_hidden(esk8_0,X2)
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_55,plain,(
    ! [X80,X81,X82] :
      ( ~ v1_relat_1(X81)
      | ~ v1_funct_1(X81)
      | ~ v1_relat_1(X82)
      | ~ v1_funct_1(X82)
      | ~ r2_hidden(X80,k1_relat_1(X81))
      | k1_funct_1(k5_relat_1(X81,X82),X80) = k1_funct_1(X82,k1_funct_1(X81,X80)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r2_hidden(esk4_3(esk7_2(X3,X2),k2_relat_1(esk7_2(X3,X2)),X1),X3)
    | ~ r2_hidden(X1,k2_relat_1(esk7_2(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_49]),c_0_31]),c_0_32])])).

cnf(c_0_57,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(esk9_0),esk8_0))))
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_39])).

cnf(c_0_60,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk7_2(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_31]),c_0_32]),c_0_33]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(esk9_0),esk8_0)))) ),
    inference(ef,[status(thm)],[c_0_59])).

cnf(c_0_63,plain,
    ( k1_funct_1(X1,k1_funct_1(k6_relat_1(X2),X3)) = k1_funct_1(k7_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_17]),c_0_18]),c_0_19]),c_0_28])])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(k6_relat_1(esk9_0),esk8_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk10_0,esk9_0),esk8_0) != k1_funct_1(esk10_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,esk9_0),esk8_0) = k1_funct_1(X1,esk8_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_39])])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.42/0.59  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.42/0.59  #
% 0.42/0.59  # Preprocessing time       : 0.030 s
% 0.42/0.59  # Presaturation interreduction done
% 0.42/0.59  
% 0.42/0.59  # Proof found!
% 0.42/0.59  # SZS status Theorem
% 0.42/0.59  # SZS output start CNFRefutation
% 0.42/0.59  fof(t40_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_1)).
% 0.42/0.59  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.42/0.59  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.42/0.59  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.42/0.59  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.42/0.59  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.42/0.59  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.42/0.59  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.42/0.59  fof(t72_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 0.42/0.59  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.42/0.59  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 0.42/0.59  fof(c_0_11, plain, ![X83, X84, X85]:(((r2_hidden(X83,k1_relat_1(X85))|~r2_hidden(X83,k1_relat_1(k5_relat_1(X85,k6_relat_1(X84))))|(~v1_relat_1(X85)|~v1_funct_1(X85)))&(r2_hidden(k1_funct_1(X85,X83),X84)|~r2_hidden(X83,k1_relat_1(k5_relat_1(X85,k6_relat_1(X84))))|(~v1_relat_1(X85)|~v1_funct_1(X85))))&(~r2_hidden(X83,k1_relat_1(X85))|~r2_hidden(k1_funct_1(X85,X83),X84)|r2_hidden(X83,k1_relat_1(k5_relat_1(X85,k6_relat_1(X84))))|(~v1_relat_1(X85)|~v1_funct_1(X85)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).
% 0.42/0.59  fof(c_0_12, plain, ![X63, X64]:(~v1_relat_1(X64)|k7_relat_1(X64,X63)=k5_relat_1(k6_relat_1(X63),X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.42/0.59  fof(c_0_13, plain, ![X75]:(v1_relat_1(k6_relat_1(X75))&v1_funct_1(k6_relat_1(X75))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.42/0.59  fof(c_0_14, plain, ![X65, X66, X67, X69, X70, X71, X73]:((((r2_hidden(esk4_3(X65,X66,X67),k1_relat_1(X65))|~r2_hidden(X67,X66)|X66!=k2_relat_1(X65)|(~v1_relat_1(X65)|~v1_funct_1(X65)))&(X67=k1_funct_1(X65,esk4_3(X65,X66,X67))|~r2_hidden(X67,X66)|X66!=k2_relat_1(X65)|(~v1_relat_1(X65)|~v1_funct_1(X65))))&(~r2_hidden(X70,k1_relat_1(X65))|X69!=k1_funct_1(X65,X70)|r2_hidden(X69,X66)|X66!=k2_relat_1(X65)|(~v1_relat_1(X65)|~v1_funct_1(X65))))&((~r2_hidden(esk5_2(X65,X71),X71)|(~r2_hidden(X73,k1_relat_1(X65))|esk5_2(X65,X71)!=k1_funct_1(X65,X73))|X71=k2_relat_1(X65)|(~v1_relat_1(X65)|~v1_funct_1(X65)))&((r2_hidden(esk6_2(X65,X71),k1_relat_1(X65))|r2_hidden(esk5_2(X65,X71),X71)|X71=k2_relat_1(X65)|(~v1_relat_1(X65)|~v1_funct_1(X65)))&(esk5_2(X65,X71)=k1_funct_1(X65,esk6_2(X65,X71))|r2_hidden(esk5_2(X65,X71),X71)|X71=k2_relat_1(X65)|(~v1_relat_1(X65)|~v1_funct_1(X65)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.42/0.59  fof(c_0_15, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.42/0.59  cnf(c_0_16, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.59  cnf(c_0_17, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.59  cnf(c_0_18, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.59  cnf(c_0_19, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.59  fof(c_0_20, plain, ![X60, X61, X62]:(((r2_hidden(X60,X61)|~r2_hidden(X60,k1_relat_1(k7_relat_1(X62,X61)))|~v1_relat_1(X62))&(r2_hidden(X60,k1_relat_1(X62))|~r2_hidden(X60,k1_relat_1(k7_relat_1(X62,X61)))|~v1_relat_1(X62)))&(~r2_hidden(X60,X61)|~r2_hidden(X60,k1_relat_1(X62))|r2_hidden(X60,k1_relat_1(k7_relat_1(X62,X61)))|~v1_relat_1(X62))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.42/0.59  fof(c_0_21, plain, ![X59]:(k1_relat_1(k6_relat_1(X59))=X59&k2_relat_1(k6_relat_1(X59))=X59), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.42/0.59  cnf(c_0_22, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.42/0.59  fof(c_0_23, plain, ![X76, X77, X79]:(((v1_relat_1(esk7_2(X76,X77))&v1_funct_1(esk7_2(X76,X77)))&k1_relat_1(esk7_2(X76,X77))=X76)&(~r2_hidden(X79,X76)|k1_funct_1(esk7_2(X76,X77),X79)=X77)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.42/0.59  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t72_funct_1])).
% 0.42/0.59  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.59  cnf(c_0_26, plain, (r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X3)|~r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(X3),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_19])])).
% 0.42/0.59  cnf(c_0_27, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.59  cnf(c_0_28, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.59  cnf(c_0_29, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).
% 0.42/0.59  cnf(c_0_30, plain, (k1_funct_1(esk7_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.42/0.59  cnf(c_0_31, plain, (v1_funct_1(esk7_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.42/0.59  cnf(c_0_32, plain, (v1_relat_1(esk7_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.42/0.59  cnf(c_0_33, plain, (k1_relat_1(esk7_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.42/0.59  fof(c_0_34, negated_conjecture, ((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&(r2_hidden(esk8_0,esk9_0)&k1_funct_1(k7_relat_1(esk10_0,esk9_0),esk8_0)!=k1_funct_1(esk10_0,esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.42/0.59  cnf(c_0_35, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.59  cnf(c_0_36, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_25])).
% 0.42/0.59  cnf(c_0_37, plain, (r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X3)|~r2_hidden(X2,X3)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19]), c_0_28])])).
% 0.42/0.59  cnf(c_0_38, plain, (r2_hidden(X1,k2_relat_1(esk7_2(X2,X1)))|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])])).
% 0.42/0.59  cnf(c_0_39, negated_conjecture, (r2_hidden(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.42/0.59  cnf(c_0_40, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_35])).
% 0.42/0.59  cnf(c_0_41, plain, (~r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X3)|~r2_hidden(X2,k4_xboole_0(X4,X3))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.42/0.59  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk7_2(esk9_0,X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.42/0.59  cnf(c_0_43, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(esk9_0,X1))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.42/0.59  cnf(c_0_44, plain, (X1=k1_funct_1(X2,esk4_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.42/0.59  fof(c_0_45, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.42/0.59  cnf(c_0_46, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.42/0.59  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(X2,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(X3),X1)))))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.42/0.59  cnf(c_0_48, negated_conjecture, (r2_hidden(esk8_0,k4_xboole_0(k4_xboole_0(esk9_0,X1),X2))|r2_hidden(esk8_0,X1)|r2_hidden(esk8_0,X2)), inference(spm,[status(thm)],[c_0_40, c_0_43])).
% 0.42/0.59  cnf(c_0_49, plain, (k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_44])).
% 0.42/0.59  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.42/0.59  cnf(c_0_51, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_46])).
% 0.42/0.59  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.42/0.59  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.42/0.59  cnf(c_0_54, negated_conjecture, (r2_hidden(esk8_0,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(X1),esk8_0))))|r2_hidden(esk8_0,X2)|~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.42/0.59  fof(c_0_55, plain, ![X80, X81, X82]:(~v1_relat_1(X81)|~v1_funct_1(X81)|(~v1_relat_1(X82)|~v1_funct_1(X82)|(~r2_hidden(X80,k1_relat_1(X81))|k1_funct_1(k5_relat_1(X81,X82),X80)=k1_funct_1(X82,k1_funct_1(X81,X80))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.42/0.59  cnf(c_0_56, plain, (X1=X2|~r2_hidden(esk4_3(esk7_2(X3,X2),k2_relat_1(esk7_2(X3,X2)),X1),X3)|~r2_hidden(X1,k2_relat_1(esk7_2(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_49]), c_0_31]), c_0_32])])).
% 0.42/0.59  cnf(c_0_57, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r1_tarski(k1_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.42/0.59  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.42/0.59  cnf(c_0_59, negated_conjecture, (r2_hidden(esk8_0,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(esk9_0),esk8_0))))|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_39])).
% 0.42/0.59  cnf(c_0_60, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.42/0.59  cnf(c_0_61, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk7_2(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_31]), c_0_32]), c_0_33]), c_0_58])])).
% 0.42/0.59  cnf(c_0_62, negated_conjecture, (r2_hidden(esk8_0,k2_relat_1(esk7_2(esk9_0,k1_funct_1(k6_relat_1(esk9_0),esk8_0))))), inference(ef,[status(thm)],[c_0_59])).
% 0.42/0.59  cnf(c_0_63, plain, (k1_funct_1(X1,k1_funct_1(k6_relat_1(X2),X3))=k1_funct_1(k7_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_17]), c_0_18]), c_0_19]), c_0_28])])).
% 0.42/0.59  cnf(c_0_64, negated_conjecture, (k1_funct_1(k6_relat_1(esk9_0),esk8_0)=esk8_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.42/0.59  cnf(c_0_65, negated_conjecture, (k1_funct_1(k7_relat_1(esk10_0,esk9_0),esk8_0)!=k1_funct_1(esk10_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.42/0.59  cnf(c_0_66, negated_conjecture, (k1_funct_1(k7_relat_1(X1,esk9_0),esk8_0)=k1_funct_1(X1,esk8_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_39])])).
% 0.42/0.59  cnf(c_0_67, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.42/0.59  cnf(c_0_68, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.42/0.59  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])]), ['proof']).
% 0.42/0.59  # SZS output end CNFRefutation
% 0.42/0.59  # Proof object total steps             : 70
% 0.42/0.59  # Proof object clause steps            : 47
% 0.42/0.59  # Proof object formula steps           : 23
% 0.42/0.59  # Proof object conjectures             : 17
% 0.42/0.59  # Proof object clause conjectures      : 14
% 0.42/0.59  # Proof object formula conjectures     : 3
% 0.42/0.59  # Proof object initial clauses used    : 23
% 0.42/0.59  # Proof object initial formulas used   : 11
% 0.42/0.59  # Proof object generating inferences   : 19
% 0.42/0.59  # Proof object simplifying inferences  : 34
% 0.42/0.59  # Training examples: 0 positive, 0 negative
% 0.42/0.59  # Parsed axioms                        : 17
% 0.42/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.59  # Initial clauses                      : 48
% 0.42/0.59  # Removed in clause preprocessing      : 5
% 0.42/0.59  # Initial clauses in saturation        : 43
% 0.42/0.59  # Processed clauses                    : 2009
% 0.42/0.59  # ...of these trivial                  : 10
% 0.42/0.59  # ...subsumed                          : 1408
% 0.42/0.59  # ...remaining for further processing  : 591
% 0.42/0.59  # Other redundant clauses eliminated   : 29
% 0.42/0.59  # Clauses deleted for lack of memory   : 0
% 0.42/0.59  # Backward-subsumed                    : 28
% 0.42/0.59  # Backward-rewritten                   : 80
% 0.42/0.59  # Generated clauses                    : 10641
% 0.42/0.59  # ...of the previous two non-trivial   : 9899
% 0.42/0.59  # Contextual simplify-reflections      : 11
% 0.42/0.59  # Paramodulations                      : 10588
% 0.42/0.59  # Factorizations                       : 28
% 0.42/0.59  # Equation resolutions                 : 29
% 0.42/0.59  # Propositional unsat checks           : 0
% 0.42/0.59  #    Propositional check models        : 0
% 0.42/0.59  #    Propositional check unsatisfiable : 0
% 0.42/0.59  #    Propositional clauses             : 0
% 0.42/0.59  #    Propositional clauses after purity: 0
% 0.42/0.59  #    Propositional unsat core size     : 0
% 0.42/0.59  #    Propositional preprocessing time  : 0.000
% 0.42/0.59  #    Propositional encoding time       : 0.000
% 0.42/0.59  #    Propositional solver time         : 0.000
% 0.42/0.59  #    Success case prop preproc time    : 0.000
% 0.42/0.59  #    Success case prop encoding time   : 0.000
% 0.42/0.59  #    Success case prop solver time     : 0.000
% 0.42/0.59  # Current number of processed clauses  : 430
% 0.42/0.59  #    Positive orientable unit clauses  : 30
% 0.42/0.59  #    Positive unorientable unit clauses: 1
% 0.42/0.59  #    Negative unit clauses             : 46
% 0.42/0.59  #    Non-unit-clauses                  : 353
% 0.42/0.59  # Current number of unprocessed clauses: 7697
% 0.42/0.59  # ...number of literals in the above   : 32674
% 0.42/0.59  # Current number of archived formulas  : 0
% 0.42/0.59  # Current number of archived clauses   : 156
% 0.42/0.59  # Clause-clause subsumption calls (NU) : 30763
% 0.42/0.59  # Rec. Clause-clause subsumption calls : 16120
% 0.42/0.59  # Non-unit clause-clause subsumptions  : 705
% 0.42/0.59  # Unit Clause-clause subsumption calls : 2042
% 0.42/0.59  # Rewrite failures with RHS unbound    : 34
% 0.42/0.59  # BW rewrite match attempts            : 264
% 0.42/0.59  # BW rewrite match successes           : 16
% 0.42/0.59  # Condensation attempts                : 0
% 0.42/0.59  # Condensation successes               : 0
% 0.42/0.59  # Termbank termtop insertions          : 206834
% 0.42/0.59  
% 0.42/0.59  # -------------------------------------------------
% 0.42/0.59  # User time                : 0.232 s
% 0.42/0.59  # System time              : 0.015 s
% 0.42/0.59  # Total time               : 0.247 s
% 0.42/0.59  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

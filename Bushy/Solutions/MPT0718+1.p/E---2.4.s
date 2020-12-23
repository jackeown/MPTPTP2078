%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t173_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:20 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  78 expanded)
%              Number of clauses        :   21 (  28 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 375 expanded)
%              Number of equality atoms :   10 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t173_funct_1.p',t6_boole)).

fof(t173_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v5_funct_1(X1,X2)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => v2_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t173_funct_1.p',t173_funct_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t173_funct_1.p',dt_o_0_0_xboole_0)).

fof(d15_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_relat_1(X1)
      <=> ! [X2] :
            ~ ( r2_hidden(X2,k1_relat_1(X1))
              & v1_xboole_0(k1_funct_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t173_funct_1.p',d15_funct_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t173_funct_1.p',t7_boole)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t173_funct_1.p',d20_funct_1)).

fof(c_0_6,plain,(
    ! [X21] :
      ( ~ v1_xboole_0(X21)
      | X21 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v5_funct_1(X1,X2)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => v2_relat_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t173_funct_1])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v5_funct_1(esk1_0,esk2_0)
    & k1_relat_1(esk1_0) = k1_relat_1(esk2_0)
    & ~ v2_relat_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ v2_relat_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(X8))
        | ~ v1_xboole_0(k1_funct_1(X8,X9))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk3_1(X8),k1_relat_1(X8))
        | v2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( v1_xboole_0(k1_funct_1(X8,esk3_1(X8)))
        | v2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_funct_1])])])])])).

cnf(c_0_12,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v1_xboole_0(k1_funct_1(X1,esk3_1(X1)))
    | v2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v5_funct_1(X12,X11)
        | ~ r2_hidden(X13,k1_relat_1(X12))
        | r2_hidden(k1_funct_1(X12,X13),k1_funct_1(X11,X13))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_2(X11,X12),k1_relat_1(X12))
        | v5_funct_1(X12,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(k1_funct_1(X12,esk4_2(X11,X12)),k1_funct_1(X11,esk4_2(X11,X12)))
        | v5_funct_1(X12,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_19,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_8,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_xboole_0(k1_funct_1(esk2_0,esk3_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))
    | ~ v5_funct_1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_1(esk2_0)) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_9])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk2_0),k1_relat_1(X1))
    | ~ v5_funct_1(X1,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15]),c_0_16])]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v5_funct_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk1_0) = k1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_1(esk2_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_25]),c_0_15]),c_0_16])])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------

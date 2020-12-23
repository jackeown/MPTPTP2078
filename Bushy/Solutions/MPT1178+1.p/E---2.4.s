%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t87_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  54 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  165 ( 293 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t87_orders_2.p',d17_orders_2)).

fof(t78_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t87_orders_2.p',t78_orders_2)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t87_orders_2.p',t91_orders_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t87_orders_2.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t87_orders_2.p',dt_o_0_0_xboole_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t87_orders_2.p',fc2_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t87_orders_2.p',t87_orders_2)).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X12,X11)
        | m2_orders_2(X12,X9,X10)
        | X11 != k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m2_orders_2(X13,X9,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r2_hidden(esk3_3(X9,X10,X14),X14)
        | ~ m2_orders_2(esk3_3(X9,X10,X14),X9,X10)
        | X14 = k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk3_3(X9,X10,X14),X14)
        | m2_orders_2(esk3_3(X9,X10,X14),X9,X10)
        | X14 = k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_8,plain,(
    ! [X54,X55] :
      ( v2_struct_0(X54)
      | ~ v3_orders_2(X54)
      | ~ v4_orders_2(X54)
      | ~ v5_orders_2(X54)
      | ~ l1_orders_2(X54)
      | ~ m1_orders_1(X55,k1_orders_1(u1_struct_0(X54)))
      | m2_orders_2(k1_tarski(k1_funct_1(X55,u1_struct_0(X54))),X54,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_orders_2])])])])).

fof(c_0_9,plain,(
    ! [X60,X61,X62] :
      ( ( X61 = k1_xboole_0
        | ~ r2_hidden(X61,X60)
        | k3_tarski(X60) != k1_xboole_0 )
      & ( esk9_1(X62) != k1_xboole_0
        | k3_tarski(X62) = k1_xboole_0 )
      & ( r2_hidden(esk9_1(X62),X62)
        | k3_tarski(X62) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X53] :
      ( ~ v1_xboole_0(X53)
      | X53 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k1_tarski(k1_funct_1(X1,u1_struct_0(X2))),X3)
    | v2_struct_0(X2)
    | X3 != k4_orders_2(X2,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_17,plain,(
    ! [X69] : ~ v1_xboole_0(k1_tarski(X69)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_18,plain,
    ( k1_tarski(k1_funct_1(X1,u1_struct_0(X2))) = k1_xboole_0
    | v2_struct_0(X2)
    | k3_tarski(X3) != k1_xboole_0
    | X3 != k4_orders_2(X2,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,negated_conjecture,(
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

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_tarski(k1_funct_1(X1,u1_struct_0(X2))) = k1_xboole_0
    | v2_struct_0(X2)
    | k3_tarski(k4_orders_2(X2,X1)) != k1_xboole_0
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_19])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))
    & k3_tarski(k4_orders_2(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------

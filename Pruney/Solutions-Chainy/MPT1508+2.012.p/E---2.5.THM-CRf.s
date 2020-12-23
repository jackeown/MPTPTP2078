%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:03 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 240 expanded)
%              Number of clauses        :   40 (  80 expanded)
%              Number of leaves         :    7 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  345 (1722 expanded)
%              Number of equality atoms :   57 ( 239 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(t42_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r3_lattice3(X1,X2,X3) )
             => k16_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(t38_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X2,X3)
             => ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
                & r3_lattices(X1,k16_lattice3(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(t41_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r4_lattice3(X1,X2,X3) )
             => k15_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r4_lattice3(X20,X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_hidden(X23,X22)
        | r1_lattices(X20,X23,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( m1_subset_1(esk3_3(X20,X21,X24),u1_struct_0(X20))
        | r4_lattice3(X20,X21,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( r2_hidden(esk3_3(X20,X21,X24),X24)
        | r4_lattice3(X20,X21,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( ~ r1_lattices(X20,esk3_3(X20,X21,X24),X21)
        | r4_lattice3(X20,X21,X24)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( r2_hidden(X2,X3)
                  & r3_lattice3(X1,X2,X3) )
               => k16_lattice3(X1,X3) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_lattice3])).

cnf(c_0_11,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & r2_hidden(esk6_0,esk7_0)
    & r3_lattice3(esk5_0,esk6_0,esk7_0)
    & k16_lattice3(esk5_0,esk7_0) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r3_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X16)
        | r1_lattices(X14,X15,X17)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) )
      & ( m1_subset_1(esk2_3(X14,X15,X18),u1_struct_0(X14))
        | r3_lattice3(X14,X15,X18)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) )
      & ( r2_hidden(esk2_3(X14,X15,X18),X18)
        | r3_lattice3(X14,X15,X18)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) )
      & ( ~ r1_lattices(X14,X15,esk2_3(X14,X15,X18))
        | r3_lattice3(X14,X15,X18)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ( r3_lattices(X32,X33,k15_lattice3(X32,X34))
        | ~ r2_hidden(X33,X34)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( r3_lattices(X32,k16_lattice3(X32,X34),X33)
        | ~ r2_hidden(X33,X34)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_16,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( ( r3_lattice3(X26,X27,X28)
        | X27 != k16_lattice3(X26,X28)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r3_lattice3(X26,X29,X28)
        | r3_lattices(X26,X29,X27)
        | X27 != k16_lattice3(X26,X28)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( m1_subset_1(esk4_3(X26,X27,X30),u1_struct_0(X26))
        | ~ r3_lattice3(X26,X27,X30)
        | X27 = k16_lattice3(X26,X30)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( r3_lattice3(X26,esk4_3(X26,X27,X30),X30)
        | ~ r3_lattice3(X26,X27,X30)
        | X27 = k16_lattice3(X26,X30)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( ~ r3_lattices(X26,esk4_3(X26,X27,X30),X27)
        | ~ r3_lattice3(X26,X27,X30)
        | X27 = k16_lattice3(X26,X30)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_17,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v10_lattices(X35)
      | ~ v4_lattice3(X35)
      | ~ l3_lattices(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | ~ r2_hidden(X36,X37)
      | ~ r4_lattice3(X35,X36,X37)
      | k15_lattice3(X35,X37) = X36 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).

cnf(c_0_18,plain,
    ( esk3_3(X1,X2,k2_tarski(X3,X4)) = X4
    | esk3_3(X1,X2,k2_tarski(X3,X4)) = X3
    | r4_lattice3(X1,X2,k2_tarski(X3,X4))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r4_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk3_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( esk3_3(esk5_0,esk6_0,k2_tarski(X1,X2)) = X1
    | esk3_3(esk5_0,esk6_0,k2_tarski(X1,X2)) = X2
    | r4_lattice3(esk5_0,esk6_0,k2_tarski(X1,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | ~ r3_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_33,plain,
    ( r3_lattice3(X1,esk4_3(X1,X2,X3),X3)
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2)
    | ~ r2_hidden(esk4_3(X2,X1,X3),X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( k15_lattice3(esk5_0,X1) = esk6_0
    | ~ r4_lattice3(esk5_0,esk6_0,X1)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_27]),c_0_28]),c_0_20])]),c_0_21])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( esk3_3(esk5_0,esk6_0,k2_tarski(X1,X2)) = X1
    | r4_lattice3(esk5_0,esk6_0,k2_tarski(X1,X2))
    | ~ r1_lattices(esk5_0,X2,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattice3(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k16_lattice3(esk5_0,X2)
    | r1_lattices(esk5_0,esk4_3(esk5_0,X1,X2),esk6_0)
    | ~ r3_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(esk4_3(esk5_0,X1,X2),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27]),c_0_28]),c_0_20])]),c_0_21])).

cnf(c_0_42,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,k2_tarski(X4,esk4_3(X2,X1,X3))))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k15_lattice3(esk5_0,k2_tarski(esk6_0,X1)) = esk6_0
    | ~ r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,k2_tarski(X1,X2))
    | ~ r1_lattices(esk5_0,X1,esk6_0)
    | ~ r1_lattices(esk5_0,X2,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_38]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattices(esk5_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k16_lattice3(esk5_0,X2)
    | r1_lattices(esk5_0,esk4_3(esk5_0,X1,X2),esk6_0)
    | ~ r3_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_27]),c_0_28]),c_0_20])]),c_0_21])).

cnf(c_0_47,plain,
    ( X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk4_3(X1,X2,X3),X2)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( X1 = k16_lattice3(esk5_0,X2)
    | r3_lattices(esk5_0,esk4_3(esk5_0,X1,X2),esk6_0)
    | ~ r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,esk4_3(esk5_0,X1,X2)))
    | ~ r3_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_27]),c_0_28]),c_0_20])]),c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,X1))
    | ~ r1_lattices(esk5_0,X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k16_lattice3(esk5_0,esk7_0)
    | r1_lattices(esk5_0,esk4_3(esk5_0,X1,esk7_0),esk6_0)
    | ~ r3_lattice3(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 = k16_lattice3(esk5_0,X1)
    | ~ r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,esk4_3(esk5_0,esk6_0,X1)))
    | ~ r3_lattice3(esk5_0,esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_27]),c_0_28]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k16_lattice3(esk5_0,esk7_0)
    | r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,esk4_3(esk5_0,X1,esk7_0)))
    | ~ r3_lattice3(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_39]),c_0_19])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.80/4.98  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 4.80/4.98  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.80/4.98  #
% 4.80/4.98  # Preprocessing time       : 0.029 s
% 4.80/4.98  # Presaturation interreduction done
% 4.80/4.98  
% 4.80/4.98  # Proof found!
% 4.80/4.98  # SZS status Theorem
% 4.80/4.98  # SZS output start CNFRefutation
% 4.80/4.98  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.80/4.98  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 4.80/4.98  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 4.80/4.98  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 4.80/4.98  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 4.80/4.98  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 4.80/4.98  fof(t41_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r4_lattice3(X1,X2,X3))=>k15_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_lattice3)).
% 4.80/4.98  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 4.80/4.98  cnf(c_0_8, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 4.80/4.98  fof(c_0_9, plain, ![X20, X21, X22, X23, X24]:((~r4_lattice3(X20,X21,X22)|(~m1_subset_1(X23,u1_struct_0(X20))|(~r2_hidden(X23,X22)|r1_lattices(X20,X23,X21)))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l3_lattices(X20)))&((m1_subset_1(esk3_3(X20,X21,X24),u1_struct_0(X20))|r4_lattice3(X20,X21,X24)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l3_lattices(X20)))&((r2_hidden(esk3_3(X20,X21,X24),X24)|r4_lattice3(X20,X21,X24)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l3_lattices(X20)))&(~r1_lattices(X20,esk3_3(X20,X21,X24),X21)|r4_lattice3(X20,X21,X24)|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l3_lattices(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 4.80/4.98  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 4.80/4.98  cnf(c_0_11, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_8])).
% 4.80/4.98  cnf(c_0_12, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.80/4.98  fof(c_0_13, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&((r2_hidden(esk6_0,esk7_0)&r3_lattice3(esk5_0,esk6_0,esk7_0))&k16_lattice3(esk5_0,esk7_0)!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 4.80/4.98  fof(c_0_14, plain, ![X14, X15, X16, X17, X18]:((~r3_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X16)|r1_lattices(X14,X15,X17)))|~m1_subset_1(X15,u1_struct_0(X14))|(v2_struct_0(X14)|~l3_lattices(X14)))&((m1_subset_1(esk2_3(X14,X15,X18),u1_struct_0(X14))|r3_lattice3(X14,X15,X18)|~m1_subset_1(X15,u1_struct_0(X14))|(v2_struct_0(X14)|~l3_lattices(X14)))&((r2_hidden(esk2_3(X14,X15,X18),X18)|r3_lattice3(X14,X15,X18)|~m1_subset_1(X15,u1_struct_0(X14))|(v2_struct_0(X14)|~l3_lattices(X14)))&(~r1_lattices(X14,X15,esk2_3(X14,X15,X18))|r3_lattice3(X14,X15,X18)|~m1_subset_1(X15,u1_struct_0(X14))|(v2_struct_0(X14)|~l3_lattices(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 4.80/4.98  fof(c_0_15, plain, ![X32, X33, X34]:((r3_lattices(X32,X33,k15_lattice3(X32,X34))|~r2_hidden(X33,X34)|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))&(r3_lattices(X32,k16_lattice3(X32,X34),X33)|~r2_hidden(X33,X34)|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 4.80/4.98  fof(c_0_16, plain, ![X26, X27, X28, X29, X30]:(((r3_lattice3(X26,X27,X28)|X27!=k16_lattice3(X26,X28)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))&(~m1_subset_1(X29,u1_struct_0(X26))|(~r3_lattice3(X26,X29,X28)|r3_lattices(X26,X29,X27))|X27!=k16_lattice3(X26,X28)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26))))&((m1_subset_1(esk4_3(X26,X27,X30),u1_struct_0(X26))|~r3_lattice3(X26,X27,X30)|X27=k16_lattice3(X26,X30)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))&((r3_lattice3(X26,esk4_3(X26,X27,X30),X30)|~r3_lattice3(X26,X27,X30)|X27=k16_lattice3(X26,X30)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))&(~r3_lattices(X26,esk4_3(X26,X27,X30),X27)|~r3_lattice3(X26,X27,X30)|X27=k16_lattice3(X26,X30)|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 4.80/4.98  fof(c_0_17, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|(~r2_hidden(X36,X37)|~r4_lattice3(X35,X36,X37)|k15_lattice3(X35,X37)=X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).
% 4.80/4.98  cnf(c_0_18, plain, (esk3_3(X1,X2,k2_tarski(X3,X4))=X4|esk3_3(X1,X2,k2_tarski(X3,X4))=X3|r4_lattice3(X1,X2,k2_tarski(X3,X4))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 4.80/4.98  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_20, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_22, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.80/4.98  cnf(c_0_23, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.80/4.98  cnf(c_0_24, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.80/4.98  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 4.80/4.98  cnf(c_0_26, plain, (v2_struct_0(X1)|k15_lattice3(X1,X3)=X2|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X2,X3)|~r4_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.80/4.98  cnf(c_0_27, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_28, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 4.80/4.98  cnf(c_0_30, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk3_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.80/4.98  cnf(c_0_31, negated_conjecture, (esk3_3(esk5_0,esk6_0,k2_tarski(X1,X2))=X1|esk3_3(esk5_0,esk6_0,k2_tarski(X1,X2))=X2|r4_lattice3(esk5_0,esk6_0,k2_tarski(X1,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_32, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|~r3_lattice3(esk5_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(esk6_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_33, plain, (r3_lattice3(X1,esk4_3(X1,X2,X3),X3)|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.80/4.98  cnf(c_0_34, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)|~r2_hidden(esk4_3(X2,X1,X3),X4)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 4.80/4.98  cnf(c_0_35, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).
% 4.80/4.98  cnf(c_0_36, negated_conjecture, (k15_lattice3(esk5_0,X1)=esk6_0|~r4_lattice3(esk5_0,esk6_0,X1)|~r2_hidden(esk6_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_27]), c_0_28]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_37, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 4.80/4.98  cnf(c_0_38, negated_conjecture, (esk3_3(esk5_0,esk6_0,k2_tarski(X1,X2))=X1|r4_lattice3(esk5_0,esk6_0,k2_tarski(X1,X2))|~r1_lattices(esk5_0,X2,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_19]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_39, negated_conjecture, (r3_lattice3(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_40, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_41, negated_conjecture, (X1=k16_lattice3(esk5_0,X2)|r1_lattices(esk5_0,esk4_3(esk5_0,X1,X2),esk6_0)|~r3_lattice3(esk5_0,X1,X2)|~m1_subset_1(esk4_3(esk5_0,X1,X2),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(esk6_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27]), c_0_28]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_42, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,k2_tarski(X4,esk4_3(X2,X1,X3))))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 4.80/4.98  cnf(c_0_43, negated_conjecture, (k15_lattice3(esk5_0,k2_tarski(esk6_0,X1))=esk6_0|~r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 4.80/4.98  cnf(c_0_44, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,k2_tarski(X1,X2))|~r1_lattices(esk5_0,X1,esk6_0)|~r1_lattices(esk5_0,X2,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_38]), c_0_19]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_45, negated_conjecture, (r1_lattices(esk5_0,esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_39]), c_0_19]), c_0_40])])).
% 4.80/4.98  cnf(c_0_46, negated_conjecture, (X1=k16_lattice3(esk5_0,X2)|r1_lattices(esk5_0,esk4_3(esk5_0,X1,X2),esk6_0)|~r3_lattice3(esk5_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(esk6_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_24]), c_0_27]), c_0_28]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_47, plain, (X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk4_3(X1,X2,X3),X2)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.80/4.98  cnf(c_0_48, negated_conjecture, (X1=k16_lattice3(esk5_0,X2)|r3_lattices(esk5_0,esk4_3(esk5_0,X1,X2),esk6_0)|~r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,esk4_3(esk5_0,X1,X2)))|~r3_lattice3(esk5_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_27]), c_0_28]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_49, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,X1))|~r1_lattices(esk5_0,X1,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 4.80/4.98  cnf(c_0_50, negated_conjecture, (X1=k16_lattice3(esk5_0,esk7_0)|r1_lattices(esk5_0,esk4_3(esk5_0,X1,esk7_0),esk6_0)|~r3_lattice3(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_46, c_0_40])).
% 4.80/4.98  cnf(c_0_51, negated_conjecture, (esk6_0=k16_lattice3(esk5_0,X1)|~r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,esk4_3(esk5_0,esk6_0,X1)))|~r3_lattice3(esk5_0,esk6_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_27]), c_0_28]), c_0_19]), c_0_20])]), c_0_21])).
% 4.80/4.98  cnf(c_0_52, negated_conjecture, (X1=k16_lattice3(esk5_0,esk7_0)|r4_lattice3(esk5_0,esk6_0,k2_tarski(esk6_0,esk4_3(esk5_0,X1,esk7_0)))|~r3_lattice3(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 4.80/4.98  cnf(c_0_53, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.80/4.98  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_39]), c_0_19])]), c_0_53]), ['proof']).
% 4.80/4.98  # SZS output end CNFRefutation
% 4.80/4.98  # Proof object total steps             : 55
% 4.80/4.98  # Proof object clause steps            : 40
% 4.80/4.98  # Proof object formula steps           : 15
% 4.80/4.98  # Proof object conjectures             : 26
% 4.80/4.98  # Proof object clause conjectures      : 23
% 4.80/4.98  # Proof object formula conjectures     : 3
% 4.80/4.98  # Proof object initial clauses used    : 19
% 4.80/4.98  # Proof object initial formulas used   : 7
% 4.80/4.98  # Proof object generating inferences   : 18
% 4.80/4.98  # Proof object simplifying inferences  : 52
% 4.80/4.98  # Training examples: 0 positive, 0 negative
% 4.80/4.98  # Parsed axioms                        : 7
% 4.80/4.98  # Removed by relevancy pruning/SinE    : 0
% 4.80/4.98  # Initial clauses                      : 30
% 4.80/4.98  # Removed in clause preprocessing      : 0
% 4.80/4.98  # Initial clauses in saturation        : 30
% 4.80/4.98  # Processed clauses                    : 19612
% 4.80/4.98  # ...of these trivial                  : 192
% 4.80/4.98  # ...subsumed                          : 14736
% 4.80/4.98  # ...remaining for further processing  : 4684
% 4.80/4.98  # Other redundant clauses eliminated   : 296
% 4.80/4.98  # Clauses deleted for lack of memory   : 0
% 4.80/4.98  # Backward-subsumed                    : 302
% 4.80/4.98  # Backward-rewritten                   : 216
% 4.80/4.98  # Generated clauses                    : 344886
% 4.80/4.98  # ...of the previous two non-trivial   : 232992
% 4.80/4.98  # Contextual simplify-reflections      : 583
% 4.80/4.98  # Paramodulations                      : 344326
% 4.80/4.98  # Factorizations                       : 266
% 4.80/4.98  # Equation resolutions                 : 296
% 4.80/4.98  # Propositional unsat checks           : 0
% 4.80/4.98  #    Propositional check models        : 0
% 4.80/4.98  #    Propositional check unsatisfiable : 0
% 4.80/4.98  #    Propositional clauses             : 0
% 4.80/4.98  #    Propositional clauses after purity: 0
% 4.80/4.98  #    Propositional unsat core size     : 0
% 4.80/4.98  #    Propositional preprocessing time  : 0.000
% 4.80/4.98  #    Propositional encoding time       : 0.000
% 4.80/4.98  #    Propositional solver time         : 0.000
% 4.80/4.98  #    Success case prop preproc time    : 0.000
% 4.80/4.98  #    Success case prop encoding time   : 0.000
% 4.80/4.98  #    Success case prop solver time     : 0.000
% 4.80/4.98  # Current number of processed clauses  : 4131
% 4.80/4.98  #    Positive orientable unit clauses  : 36
% 4.80/4.98  #    Positive unorientable unit clauses: 1
% 4.80/4.98  #    Negative unit clauses             : 2
% 4.80/4.98  #    Non-unit-clauses                  : 4092
% 4.80/4.98  # Current number of unprocessed clauses: 212128
% 4.80/4.98  # ...number of literals in the above   : 1436901
% 4.80/4.98  # Current number of archived formulas  : 0
% 4.80/4.98  # Current number of archived clauses   : 548
% 4.80/4.98  # Clause-clause subsumption calls (NU) : 6469435
% 4.80/4.98  # Rec. Clause-clause subsumption calls : 837866
% 4.80/4.98  # Non-unit clause-clause subsumptions  : 15545
% 4.80/4.98  # Unit Clause-clause subsumption calls : 8285
% 4.80/4.98  # Rewrite failures with RHS unbound    : 0
% 4.80/4.98  # BW rewrite match attempts            : 3527
% 4.80/4.98  # BW rewrite match successes           : 618
% 4.80/4.98  # Condensation attempts                : 0
% 4.80/4.98  # Condensation successes               : 0
% 4.80/4.98  # Termbank termtop insertions          : 11389167
% 4.82/4.99  
% 4.82/4.99  # -------------------------------------------------
% 4.82/4.99  # User time                : 4.553 s
% 4.82/4.99  # System time              : 0.093 s
% 4.82/4.99  # Total time               : 4.647 s
% 4.82/4.99  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

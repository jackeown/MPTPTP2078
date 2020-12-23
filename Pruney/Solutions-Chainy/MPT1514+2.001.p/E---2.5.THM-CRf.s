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
% DateTime   : Thu Dec  3 11:15:05 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 502 expanded)
%              Number of clauses        :   65 ( 172 expanded)
%              Number of leaves         :   11 ( 127 expanded)
%              Depth                    :   15
%              Number of atoms          :  687 (5049 expanded)
%              Number of equality atoms :   33 (  89 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fraenkel_a_2_5_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r3_lattices(X2,X4,X5)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(t48_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ~ ( r3_lattices(X1,X4,X5)
                          & r2_hidden(X5,X3) ) ) ) )
         => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(d18_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v4_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r4_lattice3(X1,X3,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r4_lattice3(X1,X4,X2)
                 => r1_lattices(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).

fof(fraenkel_a_2_2_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r4_lattice3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(d21_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( X3 = k15_lattice3(X1,X2)
            <=> ( r4_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r4_lattice3(X1,X4,X2)
                     => r1_lattices(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(t47_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
          & k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(c_0_11,plain,(
    ! [X34,X35,X36,X39,X40,X41] :
      ( ( m1_subset_1(esk7_3(X34,X35,X36),u1_struct_0(X35))
        | ~ r2_hidden(X34,a_2_5_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( X34 = esk7_3(X34,X35,X36)
        | ~ r2_hidden(X34,a_2_5_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( m1_subset_1(esk8_3(X34,X35,X36),u1_struct_0(X35))
        | ~ r2_hidden(X34,a_2_5_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( r3_lattices(X35,esk7_3(X34,X35,X36),esk8_3(X34,X35,X36))
        | ~ r2_hidden(X34,a_2_5_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( r2_hidden(esk8_3(X34,X35,X36),X36)
        | ~ r2_hidden(X34,a_2_5_lattice3(X35,X36))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X35))
        | X34 != X40
        | ~ m1_subset_1(X41,u1_struct_0(X35))
        | ~ r3_lattices(X35,X40,X41)
        | ~ r2_hidden(X41,X39)
        | r2_hidden(X34,a_2_5_lattice3(X35,X39))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ~ ( r2_hidden(X4,X2)
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ~ ( r3_lattices(X1,X4,X5)
                            & r2_hidden(X5,X3) ) ) ) )
           => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_lattice3])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,a_2_5_lattice3(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X1,X4)
    | ~ r2_hidden(X4,X5)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,(
    ! [X54] :
      ( ~ v2_struct_0(esk9_0)
      & v10_lattices(esk9_0)
      & v4_lattice3(esk9_0)
      & l3_lattices(esk9_0)
      & ( m1_subset_1(esk12_1(X54),u1_struct_0(esk9_0))
        | ~ r2_hidden(X54,esk10_0)
        | ~ m1_subset_1(X54,u1_struct_0(esk9_0)) )
      & ( r3_lattices(esk9_0,X54,esk12_1(X54))
        | ~ r2_hidden(X54,esk10_0)
        | ~ m1_subset_1(X54,u1_struct_0(esk9_0)) )
      & ( r2_hidden(esk12_1(X54),esk11_0)
        | ~ r2_hidden(X54,esk10_0)
        | ~ m1_subset_1(X54,u1_struct_0(esk9_0)) )
      & ~ r3_lattices(esk9_0,k15_lattice3(esk9_0,esk10_0),k15_lattice3(esk9_0,esk11_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,X3)
    | ~ r3_lattices(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r3_lattices(esk9_0,X1,esk12_1(X1))
    | ~ r2_hidden(X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v4_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v10_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk12_1(X1),u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,a_2_5_lattice3(esk9_0,X2))
    | ~ r2_hidden(esk12_1(X1),X2)
    | ~ r2_hidden(X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk12_1(X1),esk11_0)
    | ~ r2_hidden(X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r4_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_hidden(X13,X12)
        | r1_lattices(X10,X13,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( r2_hidden(esk1_3(X10,X11,X14),X14)
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( ~ r1_lattices(X10,esk1_3(X10,X11,X14),X11)
        | r4_lattice3(X10,X11,X14)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_25,plain,(
    ! [X16,X17,X19,X21] :
      ( ( m1_subset_1(esk2_2(X16,X17),u1_struct_0(X16))
        | ~ v4_lattice3(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( r4_lattice3(X16,esk2_2(X16,X17),X17)
        | ~ v4_lattice3(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r4_lattice3(X16,X19,X17)
        | r1_lattices(X16,esk2_2(X16,X17),X19)
        | ~ v4_lattice3(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( m1_subset_1(esk4_2(X16,X21),u1_struct_0(X16))
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | ~ r4_lattice3(X16,X21,esk3_1(X16))
        | v4_lattice3(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( r4_lattice3(X16,esk4_2(X16,X21),esk3_1(X16))
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | ~ r4_lattice3(X16,X21,esk3_1(X16))
        | v4_lattice3(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( ~ r1_lattices(X16,X21,esk4_2(X16,X21))
        | ~ m1_subset_1(X21,u1_struct_0(X16))
        | ~ r4_lattice3(X16,X21,esk3_1(X16))
        | v4_lattice3(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,a_2_5_lattice3(esk9_0,esk11_0))
    | ~ r2_hidden(X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r4_lattice3(X1,esk2_2(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( X1 = esk7_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(esk9_0,X1,X2),a_2_5_lattice3(esk9_0,esk11_0))
    | r4_lattice3(esk9_0,X1,X2)
    | ~ r2_hidden(esk1_3(esk9_0,X1,X2),esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19])]),c_0_20])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r1_lattices(X1,X2,esk2_2(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(esk9_0,X1,esk10_0),a_2_5_lattice3(esk9_0,esk11_0))
    | r4_lattice3(esk9_0,X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19])]),c_0_20])).

fof(c_0_39,plain,(
    ! [X28,X29,X30,X32,X33] :
      ( ( m1_subset_1(esk6_3(X28,X29,X30),u1_struct_0(X29))
        | ~ r2_hidden(X28,a_2_2_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( X28 = esk6_3(X28,X29,X30)
        | ~ r2_hidden(X28,a_2_2_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( r4_lattice3(X29,esk6_3(X28,X29,X30),X30)
        | ~ r2_hidden(X28,a_2_2_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X29))
        | X28 != X33
        | ~ r4_lattice3(X29,X33,X32)
        | r2_hidden(X28,a_2_2_lattice3(X29,X32))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

cnf(c_0_40,plain,
    ( r4_lattice3(X1,esk2_2(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(esk1_3(X1,esk2_2(X1,X2),X3),X2)
    | ~ m1_subset_1(esk1_3(X1,esk2_2(X1,X2),X3),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r4_lattice3(esk9_0,X1,esk10_0)
    | m1_subset_1(esk1_3(esk9_0,X1,esk10_0),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_42,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r3_lattices(X7,X8,X9)
        | r1_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) )
      & ( ~ r1_lattices(X7,X8,X9)
        | r3_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r4_lattice3(esk9_0,esk2_2(esk9_0,X1),esk10_0)
    | ~ r2_hidden(esk1_3(esk9_0,esk2_2(esk9_0,X1),esk10_0),X1)
    | ~ m1_subset_1(esk2_2(esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17]),c_0_19])]),c_0_20])).

fof(c_0_45,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r4_lattice3(X23,X25,X24)
        | X25 != k15_lattice3(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23)
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r4_lattice3(X23,X26,X24)
        | r1_lattices(X23,X25,X26)
        | X25 != k15_lattice3(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23)
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( m1_subset_1(esk5_3(X23,X24,X25),u1_struct_0(X23))
        | ~ r4_lattice3(X23,X25,X24)
        | X25 = k15_lattice3(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23)
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( r4_lattice3(X23,esk5_3(X23,X24,X25),X24)
        | ~ r4_lattice3(X23,X25,X24)
        | X25 = k15_lattice3(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23)
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( ~ r1_lattices(X23,X25,esk5_3(X23,X24,X25))
        | ~ r4_lattice3(X23,X25,X24)
        | X25 = k15_lattice3(X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23)
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_46,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X44,X45,X46] :
      ( ( r3_lattices(X44,X45,k15_lattice3(X44,X46))
        | ~ r2_hidden(X45,X46)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( r3_lattices(X44,k16_lattice3(X44,X46),X45)
        | ~ r2_hidden(X45,X46)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_48,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v4_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v5_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v6_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v7_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v8_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v9_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r4_lattice3(esk9_0,esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),esk10_0)
    | ~ m1_subset_1(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_51,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk5_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( r1_lattices(X2,esk2_2(X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,plain,
    ( r4_lattice3(X1,esk5_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_27])).

cnf(c_0_57,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_61,plain,(
    ! [X42,X43] :
      ( v2_struct_0(X42)
      | ~ v10_lattices(X42)
      | ~ v4_lattice3(X42)
      | ~ l3_lattices(X42)
      | k15_lattice3(X42,X43) = k16_lattice3(X42,a_2_2_lattice3(X42,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_63,plain,
    ( X1 = esk6_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),a_2_2_lattice3(esk9_0,esk10_0))
    | ~ m1_subset_1(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_65,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk5_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( r3_lattices(X1,esk2_2(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_30])).

cnf(c_0_68,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk5_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(esk1_3(X1,k15_lattice3(X1,X2),X3),X2)
    | ~ m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_27])).

fof(c_0_70,plain,(
    ! [X49,X50] :
      ( ( k15_lattice3(X49,X50) = k15_lattice3(X49,a_2_5_lattice3(X49,X50))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) )
      & ( k16_lattice3(X49,X50) = k16_lattice3(X49,a_2_6_lattice3(X49,X50))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

cnf(c_0_71,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),a_2_2_lattice3(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_30]),c_0_17]),c_0_19])]),c_0_20])).

cnf(c_0_75,plain,
    ( X1 = k15_lattice3(X2,X3)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ r3_lattices(X2,X1,esk5_3(X2,X3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_46]),c_0_58]),c_0_59]),c_0_60]),c_0_66])).

cnf(c_0_76,plain,
    ( X1 = k15_lattice3(X2,X3)
    | r3_lattices(X2,esk2_2(X2,X3),esk5_3(X2,X3,X1))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_58]),c_0_59]),c_0_60]),c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( r4_lattice3(esk9_0,k15_lattice3(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),esk10_0)
    | ~ m1_subset_1(k15_lattice3(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_38]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_78,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( ~ r3_lattices(esk9_0,k15_lattice3(esk9_0,esk10_0),k15_lattice3(esk9_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_80,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_82,plain,
    ( esk2_2(X1,X2) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_30]),c_0_29])).

cnf(c_0_83,negated_conjecture,
    ( r4_lattice3(esk9_0,k15_lattice3(esk9_0,esk11_0),esk10_0)
    | ~ m1_subset_1(k15_lattice3(esk9_0,esk11_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(k15_lattice3(esk9_0,esk11_0),a_2_2_lattice3(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(k15_lattice3(esk9_0,esk11_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_83]),c_0_17]),c_0_18]),c_0_19])]),c_0_84]),c_0_20])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_78]),c_0_17]),c_0_18]),c_0_19])]),c_0_86]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:29:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 1.53/1.73  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 1.53/1.73  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.53/1.73  #
% 1.53/1.73  # Preprocessing time       : 0.046 s
% 1.53/1.73  # Presaturation interreduction done
% 1.53/1.73  
% 1.53/1.73  # Proof found!
% 1.53/1.73  # SZS status Theorem
% 1.53/1.73  # SZS output start CNFRefutation
% 1.53/1.73  fof(fraenkel_a_2_5_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_5_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X4,X5))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 1.53/1.73  fof(t48_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 1.53/1.73  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 1.53/1.73  fof(d18_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v4_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r4_lattice3(X1,X3,X2))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 1.53/1.73  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 1.53/1.73  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 1.53/1.73  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 1.53/1.73  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 1.53/1.73  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 1.53/1.73  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 1.53/1.73  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 1.53/1.73  fof(c_0_11, plain, ![X34, X35, X36, X39, X40, X41]:((((m1_subset_1(esk7_3(X34,X35,X36),u1_struct_0(X35))|~r2_hidden(X34,a_2_5_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&(X34=esk7_3(X34,X35,X36)|~r2_hidden(X34,a_2_5_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35))))&(((m1_subset_1(esk8_3(X34,X35,X36),u1_struct_0(X35))|~r2_hidden(X34,a_2_5_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&(r3_lattices(X35,esk7_3(X34,X35,X36),esk8_3(X34,X35,X36))|~r2_hidden(X34,a_2_5_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35))))&(r2_hidden(esk8_3(X34,X35,X36),X36)|~r2_hidden(X34,a_2_5_lattice3(X35,X36))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))))&(~m1_subset_1(X40,u1_struct_0(X35))|X34!=X40|(~m1_subset_1(X41,u1_struct_0(X35))|~r3_lattices(X35,X40,X41)|~r2_hidden(X41,X39))|r2_hidden(X34,a_2_5_lattice3(X35,X39))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).
% 1.53/1.73  fof(c_0_12, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))))), inference(assume_negation,[status(cth)],[t48_lattice3])).
% 1.53/1.73  cnf(c_0_13, plain, (r2_hidden(X3,a_2_5_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X1,X4)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.53/1.73  fof(c_0_14, negated_conjecture, ![X54]:((((~v2_struct_0(esk9_0)&v10_lattices(esk9_0))&v4_lattice3(esk9_0))&l3_lattices(esk9_0))&(((m1_subset_1(esk12_1(X54),u1_struct_0(esk9_0))|~r2_hidden(X54,esk10_0)|~m1_subset_1(X54,u1_struct_0(esk9_0)))&((r3_lattices(esk9_0,X54,esk12_1(X54))|~r2_hidden(X54,esk10_0)|~m1_subset_1(X54,u1_struct_0(esk9_0)))&(r2_hidden(esk12_1(X54),esk11_0)|~r2_hidden(X54,esk10_0)|~m1_subset_1(X54,u1_struct_0(esk9_0)))))&~r3_lattices(esk9_0,k15_lattice3(esk9_0,esk10_0),k15_lattice3(esk9_0,esk11_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 1.53/1.73  cnf(c_0_15, plain, (r2_hidden(X1,a_2_5_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,X3)|~r3_lattices(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_13])).
% 1.53/1.73  cnf(c_0_16, negated_conjecture, (r3_lattices(esk9_0,X1,esk12_1(X1))|~r2_hidden(X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  cnf(c_0_17, negated_conjecture, (v4_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  cnf(c_0_18, negated_conjecture, (v10_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  cnf(c_0_19, negated_conjecture, (l3_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk12_1(X1),u1_struct_0(esk9_0))|~r2_hidden(X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,a_2_5_lattice3(esk9_0,X2))|~r2_hidden(esk12_1(X1),X2)|~r2_hidden(X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 1.53/1.73  cnf(c_0_23, negated_conjecture, (r2_hidden(esk12_1(X1),esk11_0)|~r2_hidden(X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  fof(c_0_24, plain, ![X10, X11, X12, X13, X14]:((~r4_lattice3(X10,X11,X12)|(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_hidden(X13,X12)|r1_lattices(X10,X13,X11)))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&((m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&((r2_hidden(esk1_3(X10,X11,X14),X14)|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))&(~r1_lattices(X10,esk1_3(X10,X11,X14),X11)|r4_lattice3(X10,X11,X14)|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~l3_lattices(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 1.53/1.73  fof(c_0_25, plain, ![X16, X17, X19, X21]:((((m1_subset_1(esk2_2(X16,X17),u1_struct_0(X16))|~v4_lattice3(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))&(r4_lattice3(X16,esk2_2(X16,X17),X17)|~v4_lattice3(X16)|(v2_struct_0(X16)|~l3_lattices(X16))))&(~m1_subset_1(X19,u1_struct_0(X16))|(~r4_lattice3(X16,X19,X17)|r1_lattices(X16,esk2_2(X16,X17),X19))|~v4_lattice3(X16)|(v2_struct_0(X16)|~l3_lattices(X16))))&((m1_subset_1(esk4_2(X16,X21),u1_struct_0(X16))|(~m1_subset_1(X21,u1_struct_0(X16))|~r4_lattice3(X16,X21,esk3_1(X16)))|v4_lattice3(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))&((r4_lattice3(X16,esk4_2(X16,X21),esk3_1(X16))|(~m1_subset_1(X21,u1_struct_0(X16))|~r4_lattice3(X16,X21,esk3_1(X16)))|v4_lattice3(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))&(~r1_lattices(X16,X21,esk4_2(X16,X21))|(~m1_subset_1(X21,u1_struct_0(X16))|~r4_lattice3(X16,X21,esk3_1(X16)))|v4_lattice3(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).
% 1.53/1.73  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,a_2_5_lattice3(esk9_0,esk11_0))|~r2_hidden(X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.53/1.73  cnf(c_0_27, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.53/1.73  cnf(c_0_28, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.53/1.73  cnf(c_0_29, plain, (r4_lattice3(X1,esk2_2(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.53/1.73  cnf(c_0_30, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.53/1.73  cnf(c_0_31, plain, (m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.53/1.73  cnf(c_0_32, plain, (X1=esk7_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.53/1.73  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(esk9_0,X1,X2),a_2_5_lattice3(esk9_0,esk11_0))|r4_lattice3(esk9_0,X1,X2)|~r2_hidden(esk1_3(esk9_0,X1,X2),esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.53/1.73  cnf(c_0_35, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk1_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.53/1.73  cnf(c_0_36, plain, (r1_lattices(X1,X2,esk2_2(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 1.53/1.73  cnf(c_0_37, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.53/1.73  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(esk9_0,X1,esk10_0),a_2_5_lattice3(esk9_0,esk11_0))|r4_lattice3(esk9_0,X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_19])]), c_0_20])).
% 1.53/1.73  fof(c_0_39, plain, ![X28, X29, X30, X32, X33]:((((m1_subset_1(esk6_3(X28,X29,X30),u1_struct_0(X29))|~r2_hidden(X28,a_2_2_lattice3(X29,X30))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))&(X28=esk6_3(X28,X29,X30)|~r2_hidden(X28,a_2_2_lattice3(X29,X30))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))))&(r4_lattice3(X29,esk6_3(X28,X29,X30),X30)|~r2_hidden(X28,a_2_2_lattice3(X29,X30))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))))&(~m1_subset_1(X33,u1_struct_0(X29))|X28!=X33|~r4_lattice3(X29,X33,X32)|r2_hidden(X28,a_2_2_lattice3(X29,X32))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 1.53/1.73  cnf(c_0_40, plain, (r4_lattice3(X1,esk2_2(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(esk1_3(X1,esk2_2(X1,X2),X3),X2)|~m1_subset_1(esk1_3(X1,esk2_2(X1,X2),X3),u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30])).
% 1.53/1.73  cnf(c_0_41, negated_conjecture, (r4_lattice3(esk9_0,X1,esk10_0)|m1_subset_1(esk1_3(esk9_0,X1,esk10_0),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 1.53/1.73  fof(c_0_42, plain, ![X7, X8, X9]:((~r3_lattices(X7,X8,X9)|r1_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))&(~r1_lattices(X7,X8,X9)|r3_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 1.53/1.73  cnf(c_0_43, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.53/1.73  cnf(c_0_44, negated_conjecture, (r4_lattice3(esk9_0,esk2_2(esk9_0,X1),esk10_0)|~r2_hidden(esk1_3(esk9_0,esk2_2(esk9_0,X1),esk10_0),X1)|~m1_subset_1(esk2_2(esk9_0,X1),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_17]), c_0_19])]), c_0_20])).
% 1.53/1.73  fof(c_0_45, plain, ![X23, X24, X25, X26]:(((r4_lattice3(X23,X25,X24)|X25!=k15_lattice3(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))&(~m1_subset_1(X26,u1_struct_0(X23))|(~r4_lattice3(X23,X26,X24)|r1_lattices(X23,X25,X26))|X25!=k15_lattice3(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))|(v2_struct_0(X23)|~l3_lattices(X23))))&((m1_subset_1(esk5_3(X23,X24,X25),u1_struct_0(X23))|~r4_lattice3(X23,X25,X24)|X25=k15_lattice3(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))&((r4_lattice3(X23,esk5_3(X23,X24,X25),X24)|~r4_lattice3(X23,X25,X24)|X25=k15_lattice3(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))&(~r1_lattices(X23,X25,esk5_3(X23,X24,X25))|~r4_lattice3(X23,X25,X24)|X25=k15_lattice3(X23,X24)|~m1_subset_1(X25,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 1.53/1.73  cnf(c_0_46, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.53/1.73  fof(c_0_47, plain, ![X44, X45, X46]:((r3_lattices(X44,X45,k15_lattice3(X44,X46))|~r2_hidden(X45,X46)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))&(r3_lattices(X44,k16_lattice3(X44,X46),X45)|~r2_hidden(X45,X46)|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 1.53/1.73  fof(c_0_48, plain, ![X6]:(((((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))&(v4_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v5_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v6_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v7_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v8_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v9_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 1.53/1.73  cnf(c_0_49, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_43])).
% 1.53/1.73  cnf(c_0_50, negated_conjecture, (r4_lattice3(esk9_0,esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),esk10_0)|~m1_subset_1(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 1.53/1.73  cnf(c_0_51, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk5_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.53/1.73  cnf(c_0_52, plain, (m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.53/1.73  cnf(c_0_53, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.53/1.73  cnf(c_0_54, plain, (r1_lattices(X2,esk2_2(X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.53/1.73  cnf(c_0_55, plain, (r4_lattice3(X1,esk5_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.53/1.73  cnf(c_0_56, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk1_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_27])).
% 1.53/1.73  cnf(c_0_57, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.53/1.73  cnf(c_0_58, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.53/1.73  cnf(c_0_59, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.53/1.73  cnf(c_0_60, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.53/1.73  fof(c_0_61, plain, ![X42, X43]:(v2_struct_0(X42)|~v10_lattices(X42)|~v4_lattice3(X42)|~l3_lattices(X42)|k15_lattice3(X42,X43)=k16_lattice3(X42,a_2_2_lattice3(X42,X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 1.53/1.73  cnf(c_0_62, plain, (m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.53/1.73  cnf(c_0_63, plain, (X1=esk6_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.53/1.73  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),a_2_2_lattice3(esk9_0,esk10_0))|~m1_subset_1(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_65, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk5_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_51])).
% 1.53/1.73  cnf(c_0_66, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_52])).
% 1.53/1.73  cnf(c_0_67, plain, (r3_lattices(X1,esk2_2(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_30])).
% 1.53/1.73  cnf(c_0_68, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk5_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_55])).
% 1.53/1.73  cnf(c_0_69, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(esk1_3(X1,k15_lattice3(X1,X2),X3),X2)|~m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_27])).
% 1.53/1.73  fof(c_0_70, plain, ![X49, X50]:((k15_lattice3(X49,X50)=k15_lattice3(X49,a_2_5_lattice3(X49,X50))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49)))&(k16_lattice3(X49,X50)=k16_lattice3(X49,a_2_6_lattice3(X49,X50))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 1.53/1.73  cnf(c_0_71, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.53/1.73  cnf(c_0_72, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.53/1.73  cnf(c_0_73, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.53/1.73  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),a_2_2_lattice3(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_30]), c_0_17]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_75, plain, (X1=k15_lattice3(X2,X3)|v2_struct_0(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~r3_lattices(X2,X1,esk5_3(X2,X3,X1))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_46]), c_0_58]), c_0_59]), c_0_60]), c_0_66])).
% 1.53/1.73  cnf(c_0_76, plain, (X1=k15_lattice3(X2,X3)|r3_lattices(X2,esk2_2(X2,X3),esk5_3(X2,X3,X1))|v2_struct_0(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_58]), c_0_59]), c_0_60]), c_0_66])).
% 1.53/1.73  cnf(c_0_77, negated_conjecture, (r4_lattice3(esk9_0,k15_lattice3(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),esk10_0)|~m1_subset_1(k15_lattice3(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_38]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_78, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.53/1.73  cnf(c_0_79, negated_conjecture, (~r3_lattices(esk9_0,k15_lattice3(esk9_0,esk10_0),k15_lattice3(esk9_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.53/1.73  cnf(c_0_80, plain, (r3_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X3,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 1.53/1.73  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk2_2(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_82, plain, (esk2_2(X1,X2)=k15_lattice3(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_30]), c_0_29])).
% 1.53/1.73  cnf(c_0_83, negated_conjecture, (r4_lattice3(esk9_0,k15_lattice3(esk9_0,esk11_0),esk10_0)|~m1_subset_1(k15_lattice3(esk9_0,esk11_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_84, negated_conjecture, (~r2_hidden(k15_lattice3(esk9_0,esk11_0),a_2_2_lattice3(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_85, negated_conjecture, (m1_subset_1(k15_lattice3(esk9_0,a_2_5_lattice3(esk9_0,esk11_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 1.53/1.73  cnf(c_0_86, negated_conjecture, (~m1_subset_1(k15_lattice3(esk9_0,esk11_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_83]), c_0_17]), c_0_18]), c_0_19])]), c_0_84]), c_0_20])).
% 1.53/1.73  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_78]), c_0_17]), c_0_18]), c_0_19])]), c_0_86]), c_0_20]), ['proof']).
% 1.53/1.73  # SZS output end CNFRefutation
% 1.53/1.73  # Proof object total steps             : 88
% 1.53/1.73  # Proof object clause steps            : 65
% 1.53/1.73  # Proof object formula steps           : 23
% 1.53/1.73  # Proof object conjectures             : 27
% 1.53/1.73  # Proof object clause conjectures      : 24
% 1.53/1.73  # Proof object formula conjectures     : 3
% 1.53/1.73  # Proof object initial clauses used    : 33
% 1.53/1.73  # Proof object initial formulas used   : 11
% 1.53/1.73  # Proof object generating inferences   : 27
% 1.53/1.73  # Proof object simplifying inferences  : 91
% 1.53/1.73  # Training examples: 0 positive, 0 negative
% 1.53/1.73  # Parsed axioms                        : 12
% 1.53/1.73  # Removed by relevancy pruning/SinE    : 0
% 1.53/1.73  # Initial clauses                      : 49
% 1.53/1.73  # Removed in clause preprocessing      : 1
% 1.53/1.73  # Initial clauses in saturation        : 48
% 1.53/1.73  # Processed clauses                    : 10094
% 1.53/1.73  # ...of these trivial                  : 86
% 1.53/1.73  # ...subsumed                          : 7362
% 1.53/1.73  # ...remaining for further processing  : 2646
% 1.53/1.73  # Other redundant clauses eliminated   : 32
% 1.53/1.73  # Clauses deleted for lack of memory   : 0
% 1.53/1.73  # Backward-subsumed                    : 220
% 1.53/1.73  # Backward-rewritten                   : 419
% 1.53/1.73  # Generated clauses                    : 61014
% 1.53/1.73  # ...of the previous two non-trivial   : 58643
% 1.53/1.73  # Contextual simplify-reflections      : 385
% 1.53/1.73  # Paramodulations                      : 60840
% 1.53/1.73  # Factorizations                       : 0
% 1.53/1.73  # Equation resolutions                 : 174
% 1.53/1.73  # Propositional unsat checks           : 0
% 1.53/1.73  #    Propositional check models        : 0
% 1.53/1.73  #    Propositional check unsatisfiable : 0
% 1.53/1.73  #    Propositional clauses             : 0
% 1.53/1.73  #    Propositional clauses after purity: 0
% 1.53/1.73  #    Propositional unsat core size     : 0
% 1.53/1.73  #    Propositional preprocessing time  : 0.000
% 1.53/1.73  #    Propositional encoding time       : 0.000
% 1.53/1.73  #    Propositional solver time         : 0.000
% 1.53/1.73  #    Success case prop preproc time    : 0.000
% 1.53/1.73  #    Success case prop encoding time   : 0.000
% 1.53/1.73  #    Success case prop solver time     : 0.000
% 1.53/1.73  # Current number of processed clauses  : 1957
% 1.53/1.73  #    Positive orientable unit clauses  : 43
% 1.53/1.73  #    Positive unorientable unit clauses: 0
% 1.53/1.73  #    Negative unit clauses             : 25
% 1.53/1.73  #    Non-unit-clauses                  : 1889
% 1.53/1.73  # Current number of unprocessed clauses: 48118
% 1.53/1.73  # ...number of literals in the above   : 317284
% 1.53/1.73  # Current number of archived formulas  : 0
% 1.53/1.73  # Current number of archived clauses   : 687
% 1.53/1.73  # Clause-clause subsumption calls (NU) : 687712
% 1.53/1.73  # Rec. Clause-clause subsumption calls : 128461
% 1.53/1.73  # Non-unit clause-clause subsumptions  : 7027
% 1.53/1.73  # Unit Clause-clause subsumption calls : 11144
% 1.53/1.73  # Rewrite failures with RHS unbound    : 0
% 1.53/1.73  # BW rewrite match attempts            : 433
% 1.53/1.73  # BW rewrite match successes           : 13
% 1.53/1.73  # Condensation attempts                : 0
% 1.53/1.73  # Condensation successes               : 0
% 1.53/1.73  # Termbank termtop insertions          : 2268733
% 1.53/1.73  
% 1.53/1.73  # -------------------------------------------------
% 1.53/1.73  # User time                : 1.343 s
% 1.53/1.73  # System time              : 0.037 s
% 1.53/1.73  # Total time               : 1.380 s
% 1.53/1.73  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

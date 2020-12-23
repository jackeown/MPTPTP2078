%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:07 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  132 (46788 expanded)
%              Number of clauses        :  105 (16433 expanded)
%              Number of leaves         :   13 (11191 expanded)
%              Depth                    :   25
%              Number of atoms          :  646 (362181 expanded)
%              Number of equality atoms :  127 (33428 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1)
        & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(d13_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_lattices(X1,X2,X3) = X2
                  & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

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

fof(d6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v6_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1)
          & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t50_lattice3])).

fof(c_0_14,plain,(
    ! [X15] :
      ( ( l1_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( l2_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk11_0)
    & v10_lattices(esk11_0)
    & v4_lattice3(esk11_0)
    & l3_lattices(esk11_0)
    & ( v2_struct_0(esk11_0)
      | ~ v10_lattices(esk11_0)
      | ~ v13_lattices(esk11_0)
      | ~ l3_lattices(esk11_0)
      | k5_lattices(esk11_0) != k15_lattice3(esk11_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ( k2_zfmisc_1(X5,X6) != k1_xboole_0
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r4_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_hidden(X27,X26)
        | r1_lattices(X24,X27,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))
        | r4_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( r2_hidden(esk4_3(X24,X25,X28),X28)
        | r4_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( ~ r1_lattices(X24,esk4_3(X24,X25,X28),X25)
        | r4_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_18,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_lattices(X14)
      | m1_subset_1(k5_lattices(X14),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_19,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l3_lattices(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X19,X21,X22] :
      ( ( m1_subset_1(esk2_1(X19),u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,esk2_1(X19),X21) = esk2_1(X19)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X21,esk2_1(X19)) = esk2_1(X19)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( m1_subset_1(esk3_2(X19,X22),u1_struct_0(X19))
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X22,esk3_2(X19,X22)) != X22
        | k2_lattices(X19,esk3_2(X19,X22),X22) != X22
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_22,plain,(
    ! [X30,X31,X33,X35] :
      ( ( m1_subset_1(esk5_2(X30,X31),u1_struct_0(X30))
        | ~ v4_lattice3(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( r4_lattice3(X30,esk5_2(X30,X31),X31)
        | ~ v4_lattice3(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r4_lattice3(X30,X33,X31)
        | r1_lattices(X30,esk5_2(X30,X31),X33)
        | ~ v4_lattice3(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( m1_subset_1(esk7_2(X30,X35),u1_struct_0(X30))
        | ~ m1_subset_1(X35,u1_struct_0(X30))
        | ~ r4_lattice3(X30,X35,esk6_1(X30))
        | v4_lattice3(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( r4_lattice3(X30,esk7_2(X30,X35),esk6_1(X30))
        | ~ m1_subset_1(X35,u1_struct_0(X30))
        | ~ r4_lattice3(X30,X35,esk6_1(X30))
        | v4_lattice3(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( ~ r1_lattices(X30,X35,esk7_2(X30,X35))
        | ~ m1_subset_1(X35,u1_struct_0(X30))
        | ~ r4_lattice3(X30,X35,esk6_1(X30))
        | v4_lattice3(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).

fof(c_0_23,plain,(
    ! [X37,X38,X39,X40] :
      ( ( r4_lattice3(X37,X39,X38)
        | X39 != k15_lattice3(X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37)
        | v2_struct_0(X37)
        | ~ l3_lattices(X37) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ r4_lattice3(X37,X40,X38)
        | r1_lattices(X37,X39,X40)
        | X39 != k15_lattice3(X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37)
        | v2_struct_0(X37)
        | ~ l3_lattices(X37) )
      & ( m1_subset_1(esk8_3(X37,X38,X39),u1_struct_0(X37))
        | ~ r4_lattice3(X37,X39,X38)
        | X39 = k15_lattice3(X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37)
        | v2_struct_0(X37)
        | ~ l3_lattices(X37) )
      & ( r4_lattice3(X37,esk8_3(X37,X38,X39),X38)
        | ~ r4_lattice3(X37,X39,X38)
        | X39 = k15_lattice3(X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37)
        | v2_struct_0(X37)
        | ~ l3_lattices(X37) )
      & ( ~ r1_lattices(X37,X39,esk8_3(X37,X38,X39))
        | ~ r4_lattice3(X37,X39,X38)
        | X39 = k15_lattice3(X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37)
        | v2_struct_0(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_24,plain,(
    ! [X7,X8] : ~ r2_hidden(X7,k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( l1_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_30,plain,(
    ! [X10,X11,X12] :
      ( ( k2_lattices(X10,X11,X12) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X12,X11) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X11,esk1_2(X10,X11)) != X11
        | k2_lattices(X10,esk1_2(X10,X11),X11) != X11
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v4_lattice3(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r4_lattice3(esk11_0,X1,X2)
    | r2_hidden(esk4_3(esk11_0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk11_0),u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_27])).

cnf(c_0_39,plain,
    ( r4_lattice3(X1,esk8_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk8_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_41,plain,(
    ! [X9] :
      ( ( ~ v2_struct_0(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v4_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v5_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v6_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v7_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v9_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_42,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_2(esk11_0,X1),u1_struct_0(esk11_0))
    | v13_lattices(esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_2(esk11_0,X1),u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20])]),c_0_27])).

cnf(c_0_45,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( v10_lattices(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r4_lattice3(esk11_0,k5_lattices(esk11_0),X1)
    | r2_hidden(esk4_3(esk11_0,k5_lattices(esk11_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(esk11_0)
    | ~ v10_lattices(esk11_0)
    | ~ v13_lattices(esk11_0)
    | ~ l3_lattices(esk11_0)
    | k5_lattices(esk11_0) != k15_lattice3(esk11_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk8_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( r4_lattice3(X1,esk5_2(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk8_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_40])).

fof(c_0_53,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v6_lattices(X42)
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | k2_lattices(X42,X43,X44) = k2_lattices(X42,X44,X43)
        | v2_struct_0(X42)
        | ~ l1_lattices(X42) )
      & ( m1_subset_1(esk9_1(X42),u1_struct_0(X42))
        | v6_lattices(X42)
        | v2_struct_0(X42)
        | ~ l1_lattices(X42) )
      & ( m1_subset_1(esk10_1(X42),u1_struct_0(X42))
        | v6_lattices(X42)
        | v2_struct_0(X42)
        | ~ l1_lattices(X42) )
      & ( k2_lattices(X42,esk9_1(X42),esk10_1(X42)) != k2_lattices(X42,esk10_1(X42),esk9_1(X42))
        | v6_lattices(X42)
        | v2_struct_0(X42)
        | ~ l1_lattices(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_54,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( k2_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0))
    | v13_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( X1 = k15_lattice3(esk11_0,X2)
    | m1_subset_1(esk8_3(esk11_0,X2,X1),u1_struct_0(esk11_0))
    | ~ r4_lattice3(esk11_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_33]),c_0_46]),c_0_20])]),c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( r4_lattice3(esk11_0,k5_lattices(esk11_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k15_lattice3(esk11_0,k1_xboole_0) != k5_lattices(esk11_0)
    | ~ v13_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_20]),c_0_46])]),c_0_27])).

cnf(c_0_60,plain,
    ( r1_lattices(X2,esk5_2(X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k15_lattice3(esk11_0,X2)
    | r4_lattice3(esk11_0,esk8_3(esk11_0,X2,X1),X2)
    | ~ r4_lattice3(esk11_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_33]),c_0_46]),c_0_20])]),c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( r4_lattice3(esk11_0,esk5_2(esk11_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_20])]),c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k15_lattice3(esk11_0,X2)
    | ~ r4_lattice3(esk11_0,X1,X2)
    | ~ r1_lattices(esk11_0,X1,esk8_3(esk11_0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_33]),c_0_46]),c_0_20])]),c_0_27])).

cnf(c_0_64,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( v6_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_20])]),c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),X1) = k5_lattices(esk11_0)
    | m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X2)),u1_struct_0(esk11_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_29])]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0)
    | m1_subset_1(esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_38])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0))
    | k15_lattice3(esk11_0,k1_xboole_0) != k5_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(esk11_0,esk5_2(esk11_0,X1),X2)
    | ~ r4_lattice3(esk11_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_33]),c_0_20])]),c_0_27])).

cnf(c_0_70,negated_conjecture,
    ( esk5_2(esk11_0,X1) = k15_lattice3(esk11_0,X1)
    | r4_lattice3(esk11_0,esk8_3(esk11_0,X1,esk5_2(esk11_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_44])])).

cnf(c_0_71,negated_conjecture,
    ( esk5_2(esk11_0,X1) = k15_lattice3(esk11_0,X1)
    | m1_subset_1(esk8_3(esk11_0,X1,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_62]),c_0_44])])).

cnf(c_0_72,negated_conjecture,
    ( esk5_2(esk11_0,X1) = k15_lattice3(esk11_0,X1)
    | ~ r1_lattices(esk11_0,esk5_2(esk11_0,X1),esk8_3(esk11_0,X1,esk5_2(esk11_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_62]),c_0_44])])).

fof(c_0_73,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_lattices(X16,X17,X18)
        | k2_lattices(X16,X17,X18) = X17
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16) )
      & ( k2_lattices(X16,X17,X18) != X17
        | r1_lattices(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_74,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_75,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_76,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( k2_lattices(esk11_0,X1,X2) = k2_lattices(esk11_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk11_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_29]),c_0_65])]),c_0_27])).

cnf(c_0_78,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( esk5_2(esk11_0,X1) = k15_lattice3(esk11_0,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_80,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( v9_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_46]),c_0_20])]),c_0_27])).

cnf(c_0_82,negated_conjecture,
    ( v8_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_46]),c_0_20])]),c_0_27])).

cnf(c_0_83,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_76]),c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( k2_lattices(esk11_0,X1,k5_lattices(esk11_0)) = k2_lattices(esk11_0,k5_lattices(esk11_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_38])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | m1_subset_1(esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),u1_struct_0(esk11_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k2_lattices(esk11_0,X1,X2) = X1
    | ~ r1_lattices(esk11_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk11_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_20])]),c_0_27])).

cnf(c_0_87,negated_conjecture,
    ( r1_lattices(esk11_0,esk5_2(esk11_0,k1_xboole_0),k5_lattices(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_58]),c_0_38])])).

cnf(c_0_88,negated_conjecture,
    ( k2_lattices(esk11_0,X1,k5_lattices(esk11_0)) = k5_lattices(esk11_0)
    | m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X2)),u1_struct_0(esk11_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_56]),c_0_29])]),c_0_27])).

cnf(c_0_89,negated_conjecture,
    ( k2_lattices(esk11_0,esk5_2(esk11_0,X1),k5_lattices(esk11_0)) = k2_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_44])).

cnf(c_0_90,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_91,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | r4_lattice3(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),X2)
    | r2_hidden(esk4_3(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),X2),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k2_lattices(esk11_0,esk5_2(esk11_0,k1_xboole_0),k5_lattices(esk11_0)) = esk5_2(esk11_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_38]),c_0_44])])).

cnf(c_0_93,negated_conjecture,
    ( k2_lattices(esk11_0,X1,esk5_2(esk11_0,X2)) = k2_lattices(esk11_0,esk5_2(esk11_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_44])).

cnf(c_0_94,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,X1)) = k5_lattices(esk11_0)
    | m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X2)),u1_struct_0(esk11_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_44]),c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( v13_lattices(esk11_0)
    | k2_lattices(esk11_0,X1,esk3_2(esk11_0,X1)) != X1
    | k2_lattices(esk11_0,esk3_2(esk11_0,X1),X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_29]),c_0_27])).

cnf(c_0_96,negated_conjecture,
    ( r1_lattices(esk11_0,k15_lattice3(esk11_0,X1),X2)
    | ~ r4_lattice3(esk11_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk11_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_79])).

cnf(c_0_97,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | r4_lattice3(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,k1_xboole_0)) = esk5_2(esk11_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_89])).

cnf(c_0_99,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_100,negated_conjecture,
    ( k2_lattices(esk11_0,X1,k15_lattice3(esk11_0,X2)) = k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_79]),c_0_79])).

cnf(c_0_101,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,X1)) = k5_lattices(esk11_0)
    | m1_subset_1(esk3_2(esk11_0,k15_lattice3(esk11_0,X2)),u1_struct_0(esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_79]),c_0_79])).

cnf(c_0_102,negated_conjecture,
    ( v13_lattices(esk11_0)
    | k2_lattices(esk11_0,esk5_2(esk11_0,X1),esk3_2(esk11_0,esk5_2(esk11_0,X1))) != esk5_2(esk11_0,X1)
    | k2_lattices(esk11_0,esk3_2(esk11_0,esk5_2(esk11_0,X1)),esk5_2(esk11_0,X1)) != esk5_2(esk11_0,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_44])).

cnf(c_0_103,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | r1_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),esk3_2(esk11_0,k15_lattice3(esk11_0,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_85])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk11_0,X1),u1_struct_0(esk11_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_79])).

cnf(c_0_105,negated_conjecture,
    ( esk5_2(esk11_0,k1_xboole_0) = k5_lattices(esk11_0)
    | ~ r1_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_98]),c_0_44]),c_0_38])])).

cnf(c_0_106,negated_conjecture,
    ( r1_lattices(esk11_0,X1,X2)
    | k2_lattices(esk11_0,X1,X2) != X1
    | ~ m1_subset_1(X2,u1_struct_0(esk11_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_81]),c_0_82]),c_0_20])]),c_0_27])).

cnf(c_0_107,negated_conjecture,
    ( k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X2)) = k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))
    | k2_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,X3)) = k5_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( v13_lattices(esk11_0)
    | k2_lattices(esk11_0,k15_lattice3(esk11_0,X1),esk3_2(esk11_0,k15_lattice3(esk11_0,X1))) != k15_lattice3(esk11_0,X1)
    | k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X1)) != k15_lattice3(esk11_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_79]),c_0_79]),c_0_79]),c_0_79]),c_0_79]),c_0_79])).

cnf(c_0_109,negated_conjecture,
    ( k2_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),esk3_2(esk11_0,k15_lattice3(esk11_0,X1))) = k15_lattice3(esk11_0,k1_xboole_0)
    | k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_103]),c_0_104])]),c_0_85])).

cnf(c_0_110,negated_conjecture,
    ( k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0)
    | ~ r1_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_79]),c_0_79])).

cnf(c_0_111,negated_conjecture,
    ( k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X2)) = k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))
    | r1_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_104]),c_0_38])])).

cnf(c_0_112,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | v13_lattices(esk11_0)
    | k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,k1_xboole_0)),k15_lattice3(esk11_0,k1_xboole_0)) != k15_lattice3(esk11_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X2)) = k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))
    | k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_114,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0)
    | v13_lattices(esk11_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | k2_lattices(esk11_0,X1,k5_lattices(esk11_0)) = k5_lattices(esk11_0)
    | k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_114]),c_0_29])]),c_0_27])).

cnf(c_0_116,negated_conjecture,
    ( k2_lattices(esk11_0,esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)),k5_lattices(esk11_0)) = k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))
    | k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_67])).

cnf(c_0_117,negated_conjecture,
    ( k2_lattices(esk11_0,esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)),k5_lattices(esk11_0)) = k5_lattices(esk11_0)
    | k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_67])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(esk3_2(esk11_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0))
    | v13_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_119,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) = k5_lattices(esk11_0)
    | k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0)
    | ~ r1_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58]),c_0_38])])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(esk3_2(esk11_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0))
    | k15_lattice3(esk11_0,k1_xboole_0) != k5_lattices(esk11_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( k15_lattice3(esk11_0,k1_xboole_0) = k5_lattices(esk11_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_119]),c_0_38])]),c_0_67]),c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(esk3_2(esk11_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122])])).

cnf(c_0_124,negated_conjecture,
    ( r4_lattice3(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),X1)
    | r2_hidden(esk4_3(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),X1),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_123])).

cnf(c_0_125,negated_conjecture,
    ( ~ v13_lattices(esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_122])])).

cnf(c_0_126,negated_conjecture,
    ( r4_lattice3(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0))) != k5_lattices(esk11_0)
    | k2_lattices(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),k5_lattices(esk11_0)) != k5_lattices(esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_122]),c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( k2_lattices(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),k5_lattices(esk11_0)) = k2_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( r1_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_126]),c_0_122]),c_0_123])])).

cnf(c_0_130,negated_conjecture,
    ( k2_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0))) != k5_lattices(esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128])])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_129]),c_0_123]),c_0_38])]),c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n024.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:42:36 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 2.62/2.79  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 2.62/2.79  # and selection function HSelectMinInfpos.
% 2.62/2.79  #
% 2.62/2.79  # Preprocessing time       : 0.031 s
% 2.62/2.79  # Presaturation interreduction done
% 2.62/2.79  
% 2.62/2.79  # Proof found!
% 2.62/2.79  # SZS status Theorem
% 2.62/2.79  # SZS output start CNFRefutation
% 2.62/2.79  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 2.62/2.79  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.62/2.79  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.62/2.79  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 2.62/2.79  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.62/2.79  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 2.62/2.79  fof(d18_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v4_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r4_lattice3(X1,X3,X2))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 2.62/2.79  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 2.62/2.79  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.62/2.79  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 2.62/2.79  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.62/2.79  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 2.62/2.79  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 2.62/2.79  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 2.62/2.79  fof(c_0_14, plain, ![X15]:((l1_lattices(X15)|~l3_lattices(X15))&(l2_lattices(X15)|~l3_lattices(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 2.62/2.79  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk11_0)&v10_lattices(esk11_0))&v4_lattice3(esk11_0))&l3_lattices(esk11_0))&(v2_struct_0(esk11_0)|~v10_lattices(esk11_0)|~v13_lattices(esk11_0)|~l3_lattices(esk11_0)|k5_lattices(esk11_0)!=k15_lattice3(esk11_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 2.62/2.79  fof(c_0_16, plain, ![X5, X6]:((k2_zfmisc_1(X5,X6)!=k1_xboole_0|(X5=k1_xboole_0|X6=k1_xboole_0))&((X5!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0)&(X6!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 2.62/2.79  fof(c_0_17, plain, ![X24, X25, X26, X27, X28]:((~r4_lattice3(X24,X25,X26)|(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_hidden(X27,X26)|r1_lattices(X24,X27,X25)))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))|r4_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((r2_hidden(esk4_3(X24,X25,X28),X28)|r4_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&(~r1_lattices(X24,esk4_3(X24,X25,X28),X25)|r4_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 2.62/2.79  fof(c_0_18, plain, ![X14]:(v2_struct_0(X14)|~l1_lattices(X14)|m1_subset_1(k5_lattices(X14),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 2.62/2.79  cnf(c_0_19, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.79  cnf(c_0_20, negated_conjecture, (l3_lattices(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.62/2.79  fof(c_0_21, plain, ![X19, X21, X22]:(((m1_subset_1(esk2_1(X19),u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&((k2_lattices(X19,esk2_1(X19),X21)=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X21,esk2_1(X19))=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))))&((m1_subset_1(esk3_2(X19,X22),u1_struct_0(X19))|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X22,esk3_2(X19,X22))!=X22|k2_lattices(X19,esk3_2(X19,X22),X22)!=X22|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 2.62/2.79  fof(c_0_22, plain, ![X30, X31, X33, X35]:((((m1_subset_1(esk5_2(X30,X31),u1_struct_0(X30))|~v4_lattice3(X30)|(v2_struct_0(X30)|~l3_lattices(X30)))&(r4_lattice3(X30,esk5_2(X30,X31),X31)|~v4_lattice3(X30)|(v2_struct_0(X30)|~l3_lattices(X30))))&(~m1_subset_1(X33,u1_struct_0(X30))|(~r4_lattice3(X30,X33,X31)|r1_lattices(X30,esk5_2(X30,X31),X33))|~v4_lattice3(X30)|(v2_struct_0(X30)|~l3_lattices(X30))))&((m1_subset_1(esk7_2(X30,X35),u1_struct_0(X30))|(~m1_subset_1(X35,u1_struct_0(X30))|~r4_lattice3(X30,X35,esk6_1(X30)))|v4_lattice3(X30)|(v2_struct_0(X30)|~l3_lattices(X30)))&((r4_lattice3(X30,esk7_2(X30,X35),esk6_1(X30))|(~m1_subset_1(X35,u1_struct_0(X30))|~r4_lattice3(X30,X35,esk6_1(X30)))|v4_lattice3(X30)|(v2_struct_0(X30)|~l3_lattices(X30)))&(~r1_lattices(X30,X35,esk7_2(X30,X35))|(~m1_subset_1(X35,u1_struct_0(X30))|~r4_lattice3(X30,X35,esk6_1(X30)))|v4_lattice3(X30)|(v2_struct_0(X30)|~l3_lattices(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).
% 2.62/2.79  fof(c_0_23, plain, ![X37, X38, X39, X40]:(((r4_lattice3(X37,X39,X38)|X39!=k15_lattice3(X37,X38)|~m1_subset_1(X39,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37))|(v2_struct_0(X37)|~l3_lattices(X37)))&(~m1_subset_1(X40,u1_struct_0(X37))|(~r4_lattice3(X37,X40,X38)|r1_lattices(X37,X39,X40))|X39!=k15_lattice3(X37,X38)|~m1_subset_1(X39,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37))|(v2_struct_0(X37)|~l3_lattices(X37))))&((m1_subset_1(esk8_3(X37,X38,X39),u1_struct_0(X37))|~r4_lattice3(X37,X39,X38)|X39=k15_lattice3(X37,X38)|~m1_subset_1(X39,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37))|(v2_struct_0(X37)|~l3_lattices(X37)))&((r4_lattice3(X37,esk8_3(X37,X38,X39),X38)|~r4_lattice3(X37,X39,X38)|X39=k15_lattice3(X37,X38)|~m1_subset_1(X39,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37))|(v2_struct_0(X37)|~l3_lattices(X37)))&(~r1_lattices(X37,X39,esk8_3(X37,X38,X39))|~r4_lattice3(X37,X39,X38)|X39=k15_lattice3(X37,X38)|~m1_subset_1(X39,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37))|(v2_struct_0(X37)|~l3_lattices(X37)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 2.62/2.79  fof(c_0_24, plain, ![X7, X8]:~r2_hidden(X7,k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 2.62/2.79  cnf(c_0_25, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.62/2.79  cnf(c_0_26, plain, (r2_hidden(esk4_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.62/2.79  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.62/2.79  cnf(c_0_28, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.62/2.79  cnf(c_0_29, negated_conjecture, (l1_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.62/2.79  fof(c_0_30, plain, ![X10, X11, X12]:(((k2_lattices(X10,X11,X12)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X12,X11)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))&((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X11,esk1_2(X10,X11))!=X11|k2_lattices(X10,esk1_2(X10,X11),X11)!=X11|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 2.62/2.79  cnf(c_0_31, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.62/2.79  cnf(c_0_32, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.62/2.79  cnf(c_0_33, negated_conjecture, (v4_lattice3(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.62/2.79  cnf(c_0_34, plain, (m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.62/2.79  cnf(c_0_35, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.62/2.79  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 2.62/2.79  cnf(c_0_37, negated_conjecture, (r4_lattice3(esk11_0,X1,X2)|r2_hidden(esk4_3(esk11_0,X1,X2),X2)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_27])).
% 2.62/2.79  cnf(c_0_38, negated_conjecture, (m1_subset_1(k5_lattices(esk11_0),u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_27])).
% 2.62/2.79  cnf(c_0_39, plain, (r4_lattice3(X1,esk8_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.62/2.79  cnf(c_0_40, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk8_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.62/2.79  fof(c_0_41, plain, ![X9]:(((((((~v2_struct_0(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))&(v4_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v5_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v6_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v7_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v8_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v9_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 2.62/2.79  cnf(c_0_42, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|X2!=k5_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.62/2.79  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk3_2(esk11_0,X1),u1_struct_0(esk11_0))|v13_lattices(esk11_0)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_27])).
% 2.62/2.79  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_2(esk11_0,X1),u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_45, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_34])).
% 2.62/2.79  cnf(c_0_46, negated_conjecture, (v10_lattices(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.62/2.79  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.62/2.79  cnf(c_0_48, negated_conjecture, (r4_lattice3(esk11_0,k5_lattices(esk11_0),X1)|r2_hidden(esk4_3(esk11_0,k5_lattices(esk11_0),X1),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.62/2.79  cnf(c_0_49, negated_conjecture, (v2_struct_0(esk11_0)|~v10_lattices(esk11_0)|~v13_lattices(esk11_0)|~l3_lattices(esk11_0)|k5_lattices(esk11_0)!=k15_lattice3(esk11_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.62/2.79  cnf(c_0_50, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk8_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_39])).
% 2.62/2.79  cnf(c_0_51, plain, (r4_lattice3(X1,esk5_2(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.62/2.79  cnf(c_0_52, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk8_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_40])).
% 2.62/2.79  fof(c_0_53, plain, ![X42, X43, X44]:((~v6_lattices(X42)|(~m1_subset_1(X43,u1_struct_0(X42))|(~m1_subset_1(X44,u1_struct_0(X42))|k2_lattices(X42,X43,X44)=k2_lattices(X42,X44,X43)))|(v2_struct_0(X42)|~l1_lattices(X42)))&((m1_subset_1(esk9_1(X42),u1_struct_0(X42))|v6_lattices(X42)|(v2_struct_0(X42)|~l1_lattices(X42)))&((m1_subset_1(esk10_1(X42),u1_struct_0(X42))|v6_lattices(X42)|(v2_struct_0(X42)|~l1_lattices(X42)))&(k2_lattices(X42,esk9_1(X42),esk10_1(X42))!=k2_lattices(X42,esk10_1(X42),esk9_1(X42))|v6_lattices(X42)|(v2_struct_0(X42)|~l1_lattices(X42)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 2.62/2.79  cnf(c_0_54, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.62/2.79  cnf(c_0_55, plain, (k2_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]), c_0_28])).
% 2.62/2.79  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0))|v13_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.62/2.79  cnf(c_0_57, negated_conjecture, (X1=k15_lattice3(esk11_0,X2)|m1_subset_1(esk8_3(esk11_0,X2,X1),u1_struct_0(esk11_0))|~r4_lattice3(esk11_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_33]), c_0_46]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_58, negated_conjecture, (r4_lattice3(esk11_0,k5_lattices(esk11_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 2.62/2.79  cnf(c_0_59, negated_conjecture, (k15_lattice3(esk11_0,k1_xboole_0)!=k5_lattices(esk11_0)|~v13_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_20]), c_0_46])]), c_0_27])).
% 2.62/2.79  cnf(c_0_60, plain, (r1_lattices(X2,esk5_2(X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.62/2.79  cnf(c_0_61, negated_conjecture, (X1=k15_lattice3(esk11_0,X2)|r4_lattice3(esk11_0,esk8_3(esk11_0,X2,X1),X2)|~r4_lattice3(esk11_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_33]), c_0_46]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_62, negated_conjecture, (r4_lattice3(esk11_0,esk5_2(esk11_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_33]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_63, negated_conjecture, (X1=k15_lattice3(esk11_0,X2)|~r4_lattice3(esk11_0,X1,X2)|~r1_lattices(esk11_0,X1,esk8_3(esk11_0,X2,X1))|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_33]), c_0_46]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_64, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.62/2.79  cnf(c_0_65, negated_conjecture, (v6_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_46]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_66, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),X1)=k5_lattices(esk11_0)|m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X2)),u1_struct_0(esk11_0))|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_29])]), c_0_27])).
% 2.62/2.79  cnf(c_0_67, negated_conjecture, (k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)|m1_subset_1(esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_38])])).
% 2.62/2.79  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0))|k15_lattice3(esk11_0,k1_xboole_0)!=k5_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_59, c_0_56])).
% 2.62/2.79  cnf(c_0_69, negated_conjecture, (r1_lattices(esk11_0,esk5_2(esk11_0,X1),X2)|~r4_lattice3(esk11_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_33]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_70, negated_conjecture, (esk5_2(esk11_0,X1)=k15_lattice3(esk11_0,X1)|r4_lattice3(esk11_0,esk8_3(esk11_0,X1,esk5_2(esk11_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_44])])).
% 2.62/2.79  cnf(c_0_71, negated_conjecture, (esk5_2(esk11_0,X1)=k15_lattice3(esk11_0,X1)|m1_subset_1(esk8_3(esk11_0,X1,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_62]), c_0_44])])).
% 2.62/2.79  cnf(c_0_72, negated_conjecture, (esk5_2(esk11_0,X1)=k15_lattice3(esk11_0,X1)|~r1_lattices(esk11_0,esk5_2(esk11_0,X1),esk8_3(esk11_0,X1,esk5_2(esk11_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_62]), c_0_44])])).
% 2.62/2.79  fof(c_0_73, plain, ![X16, X17, X18]:((~r1_lattices(X16,X17,X18)|k2_lattices(X16,X17,X18)=X17|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))&(k2_lattices(X16,X17,X18)!=X17|r1_lattices(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 2.62/2.79  cnf(c_0_74, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.62/2.79  cnf(c_0_75, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.62/2.79  cnf(c_0_76, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.62/2.79  cnf(c_0_77, negated_conjecture, (k2_lattices(esk11_0,X1,X2)=k2_lattices(esk11_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk11_0))|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_29]), c_0_65])]), c_0_27])).
% 2.62/2.79  cnf(c_0_78, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X1)),u1_struct_0(esk11_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 2.62/2.79  cnf(c_0_79, negated_conjecture, (esk5_2(esk11_0,X1)=k15_lattice3(esk11_0,X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72])).
% 2.62/2.79  cnf(c_0_80, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.62/2.79  cnf(c_0_81, negated_conjecture, (v9_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_46]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_82, negated_conjecture, (v8_lattices(esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_46]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_83, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_76]), c_0_28])).
% 2.62/2.79  cnf(c_0_84, negated_conjecture, (k2_lattices(esk11_0,X1,k5_lattices(esk11_0))=k2_lattices(esk11_0,k5_lattices(esk11_0),X1)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(spm,[status(thm)],[c_0_77, c_0_38])).
% 2.62/2.79  cnf(c_0_85, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|m1_subset_1(esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),u1_struct_0(esk11_0))), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 2.62/2.79  cnf(c_0_86, negated_conjecture, (k2_lattices(esk11_0,X1,X2)=X1|~r1_lattices(esk11_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk11_0))|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_87, negated_conjecture, (r1_lattices(esk11_0,esk5_2(esk11_0,k1_xboole_0),k5_lattices(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_58]), c_0_38])])).
% 2.62/2.79  cnf(c_0_88, negated_conjecture, (k2_lattices(esk11_0,X1,k5_lattices(esk11_0))=k5_lattices(esk11_0)|m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X2)),u1_struct_0(esk11_0))|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_56]), c_0_29])]), c_0_27])).
% 2.62/2.79  cnf(c_0_89, negated_conjecture, (k2_lattices(esk11_0,esk5_2(esk11_0,X1),k5_lattices(esk11_0))=k2_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,X1))), inference(spm,[status(thm)],[c_0_84, c_0_44])).
% 2.62/2.79  cnf(c_0_90, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.62/2.79  cnf(c_0_91, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|r4_lattice3(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),X2)|r2_hidden(esk4_3(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),X2),X2)), inference(spm,[status(thm)],[c_0_37, c_0_85])).
% 2.62/2.79  cnf(c_0_92, negated_conjecture, (k2_lattices(esk11_0,esk5_2(esk11_0,k1_xboole_0),k5_lattices(esk11_0))=esk5_2(esk11_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_38]), c_0_44])])).
% 2.62/2.79  cnf(c_0_93, negated_conjecture, (k2_lattices(esk11_0,X1,esk5_2(esk11_0,X2))=k2_lattices(esk11_0,esk5_2(esk11_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(spm,[status(thm)],[c_0_77, c_0_44])).
% 2.62/2.79  cnf(c_0_94, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,X1))=k5_lattices(esk11_0)|m1_subset_1(esk3_2(esk11_0,esk5_2(esk11_0,X2)),u1_struct_0(esk11_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_44]), c_0_89])).
% 2.62/2.79  cnf(c_0_95, negated_conjecture, (v13_lattices(esk11_0)|k2_lattices(esk11_0,X1,esk3_2(esk11_0,X1))!=X1|k2_lattices(esk11_0,esk3_2(esk11_0,X1),X1)!=X1|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_29]), c_0_27])).
% 2.62/2.79  cnf(c_0_96, negated_conjecture, (r1_lattices(esk11_0,k15_lattice3(esk11_0,X1),X2)|~r4_lattice3(esk11_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk11_0))), inference(rw,[status(thm)],[c_0_69, c_0_79])).
% 2.62/2.79  cnf(c_0_97, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|r4_lattice3(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_91])).
% 2.62/2.79  cnf(c_0_98, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,k1_xboole_0))=esk5_2(esk11_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_92, c_0_89])).
% 2.62/2.79  cnf(c_0_99, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.62/2.79  cnf(c_0_100, negated_conjecture, (k2_lattices(esk11_0,X1,k15_lattice3(esk11_0,X2))=k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_79]), c_0_79])).
% 2.62/2.79  cnf(c_0_101, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,X1))=k5_lattices(esk11_0)|m1_subset_1(esk3_2(esk11_0,k15_lattice3(esk11_0,X2)),u1_struct_0(esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_79]), c_0_79])).
% 2.62/2.79  cnf(c_0_102, negated_conjecture, (v13_lattices(esk11_0)|k2_lattices(esk11_0,esk5_2(esk11_0,X1),esk3_2(esk11_0,esk5_2(esk11_0,X1)))!=esk5_2(esk11_0,X1)|k2_lattices(esk11_0,esk3_2(esk11_0,esk5_2(esk11_0,X1)),esk5_2(esk11_0,X1))!=esk5_2(esk11_0,X1)), inference(spm,[status(thm)],[c_0_95, c_0_44])).
% 2.62/2.79  cnf(c_0_103, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|r1_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_85])).
% 2.62/2.79  cnf(c_0_104, negated_conjecture, (m1_subset_1(k15_lattice3(esk11_0,X1),u1_struct_0(esk11_0))), inference(rw,[status(thm)],[c_0_44, c_0_79])).
% 2.62/2.79  cnf(c_0_105, negated_conjecture, (esk5_2(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)|~r1_lattices(esk11_0,k5_lattices(esk11_0),esk5_2(esk11_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_98]), c_0_44]), c_0_38])])).
% 2.62/2.79  cnf(c_0_106, negated_conjecture, (r1_lattices(esk11_0,X1,X2)|k2_lattices(esk11_0,X1,X2)!=X1|~m1_subset_1(X2,u1_struct_0(esk11_0))|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_81]), c_0_82]), c_0_20])]), c_0_27])).
% 2.62/2.79  cnf(c_0_107, negated_conjecture, (k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X2))=k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))|k2_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,X3))=k5_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 2.62/2.79  cnf(c_0_108, negated_conjecture, (v13_lattices(esk11_0)|k2_lattices(esk11_0,k15_lattice3(esk11_0,X1),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))!=k15_lattice3(esk11_0,X1)|k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X1))!=k15_lattice3(esk11_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_79]), c_0_79]), c_0_79]), c_0_79]), c_0_79]), c_0_79])).
% 2.62/2.79  cnf(c_0_109, negated_conjecture, (k2_lattices(esk11_0,k15_lattice3(esk11_0,k1_xboole_0),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))=k15_lattice3(esk11_0,k1_xboole_0)|k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_103]), c_0_104])]), c_0_85])).
% 2.62/2.79  cnf(c_0_110, negated_conjecture, (k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)|~r1_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_79]), c_0_79])).
% 2.62/2.79  cnf(c_0_111, negated_conjecture, (k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X2))=k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))|r1_lattices(esk11_0,k5_lattices(esk11_0),k15_lattice3(esk11_0,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_104]), c_0_38])])).
% 2.62/2.79  cnf(c_0_112, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|v13_lattices(esk11_0)|k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,k1_xboole_0)),k15_lattice3(esk11_0,k1_xboole_0))!=k15_lattice3(esk11_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 2.62/2.79  cnf(c_0_113, negated_conjecture, (k2_lattices(esk11_0,esk3_2(esk11_0,k15_lattice3(esk11_0,X1)),k15_lattice3(esk11_0,X2))=k2_lattices(esk11_0,k15_lattice3(esk11_0,X2),esk3_2(esk11_0,k15_lattice3(esk11_0,X1)))|k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 2.62/2.79  cnf(c_0_114, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)|v13_lattices(esk11_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_109])).
% 2.62/2.79  cnf(c_0_115, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|k2_lattices(esk11_0,X1,k5_lattices(esk11_0))=k5_lattices(esk11_0)|k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)|~m1_subset_1(X1,u1_struct_0(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_114]), c_0_29])]), c_0_27])).
% 2.62/2.79  cnf(c_0_116, negated_conjecture, (k2_lattices(esk11_0,esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)),k5_lattices(esk11_0))=k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))|k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_84, c_0_67])).
% 2.62/2.79  cnf(c_0_117, negated_conjecture, (k2_lattices(esk11_0,esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)),k5_lattices(esk11_0))=k5_lattices(esk11_0)|k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_115, c_0_67])).
% 2.62/2.79  cnf(c_0_118, negated_conjecture, (m1_subset_1(esk3_2(esk11_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0))|v13_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 2.62/2.79  cnf(c_0_119, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))=k5_lattices(esk11_0)|k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 2.62/2.79  cnf(c_0_120, negated_conjecture, (k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)|~r1_lattices(esk11_0,k5_lattices(esk11_0),esk8_3(esk11_0,k1_xboole_0,k5_lattices(esk11_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_58]), c_0_38])])).
% 2.62/2.79  cnf(c_0_121, negated_conjecture, (m1_subset_1(esk3_2(esk11_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0))|k15_lattice3(esk11_0,k1_xboole_0)!=k5_lattices(esk11_0)), inference(spm,[status(thm)],[c_0_59, c_0_118])).
% 2.62/2.79  cnf(c_0_122, negated_conjecture, (k15_lattice3(esk11_0,k1_xboole_0)=k5_lattices(esk11_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_119]), c_0_38])]), c_0_67]), c_0_120])).
% 2.62/2.79  cnf(c_0_123, negated_conjecture, (m1_subset_1(esk3_2(esk11_0,k5_lattices(esk11_0)),u1_struct_0(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122])])).
% 2.62/2.79  cnf(c_0_124, negated_conjecture, (r4_lattice3(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),X1)|r2_hidden(esk4_3(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),X1),X1)), inference(spm,[status(thm)],[c_0_37, c_0_123])).
% 2.62/2.79  cnf(c_0_125, negated_conjecture, (~v13_lattices(esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_122])])).
% 2.62/2.79  cnf(c_0_126, negated_conjecture, (r4_lattice3(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_124])).
% 2.62/2.79  cnf(c_0_127, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0)))!=k5_lattices(esk11_0)|k2_lattices(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),k5_lattices(esk11_0))!=k5_lattices(esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_122]), c_0_125])).
% 2.62/2.79  cnf(c_0_128, negated_conjecture, (k2_lattices(esk11_0,esk3_2(esk11_0,k5_lattices(esk11_0)),k5_lattices(esk11_0))=k2_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0)))), inference(spm,[status(thm)],[c_0_84, c_0_123])).
% 2.62/2.79  cnf(c_0_129, negated_conjecture, (r1_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_126]), c_0_122]), c_0_123])])).
% 2.62/2.79  cnf(c_0_130, negated_conjecture, (k2_lattices(esk11_0,k5_lattices(esk11_0),esk3_2(esk11_0,k5_lattices(esk11_0)))!=k5_lattices(esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128])])).
% 2.62/2.79  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_129]), c_0_123]), c_0_38])]), c_0_130]), ['proof']).
% 2.62/2.79  # SZS output end CNFRefutation
% 2.62/2.79  # Proof object total steps             : 132
% 2.62/2.79  # Proof object clause steps            : 105
% 2.62/2.79  # Proof object formula steps           : 27
% 2.62/2.79  # Proof object conjectures             : 80
% 2.62/2.79  # Proof object clause conjectures      : 77
% 2.62/2.79  # Proof object formula conjectures     : 3
% 2.62/2.79  # Proof object initial clauses used    : 26
% 2.62/2.79  # Proof object initial formulas used   : 13
% 2.62/2.79  # Proof object generating inferences   : 61
% 2.62/2.79  # Proof object simplifying inferences  : 130
% 2.62/2.79  # Training examples: 0 positive, 0 negative
% 2.62/2.79  # Parsed axioms                        : 13
% 2.62/2.79  # Removed by relevancy pruning/SinE    : 0
% 2.62/2.79  # Initial clauses                      : 49
% 2.62/2.79  # Removed in clause preprocessing      : 1
% 2.62/2.79  # Initial clauses in saturation        : 48
% 2.62/2.79  # Processed clauses                    : 8392
% 2.62/2.79  # ...of these trivial                  : 79
% 2.62/2.79  # ...subsumed                          : 3753
% 2.62/2.79  # ...remaining for further processing  : 4560
% 2.62/2.79  # Other redundant clauses eliminated   : 8
% 2.62/2.79  # Clauses deleted for lack of memory   : 0
% 2.62/2.79  # Backward-subsumed                    : 875
% 2.62/2.79  # Backward-rewritten                   : 3305
% 2.62/2.79  # Generated clauses                    : 173149
% 2.62/2.79  # ...of the previous two non-trivial   : 174326
% 2.62/2.79  # Contextual simplify-reflections      : 774
% 2.62/2.79  # Paramodulations                      : 172995
% 2.62/2.79  # Factorizations                       : 16
% 2.62/2.79  # Equation resolutions                 : 10
% 2.62/2.79  # Propositional unsat checks           : 0
% 2.62/2.79  #    Propositional check models        : 0
% 2.62/2.79  #    Propositional check unsatisfiable : 0
% 2.62/2.79  #    Propositional clauses             : 0
% 2.62/2.79  #    Propositional clauses after purity: 0
% 2.62/2.79  #    Propositional unsat core size     : 0
% 2.62/2.79  #    Propositional preprocessing time  : 0.000
% 2.62/2.79  #    Propositional encoding time       : 0.000
% 2.62/2.79  #    Propositional solver time         : 0.000
% 2.62/2.79  #    Success case prop preproc time    : 0.000
% 2.62/2.79  #    Success case prop encoding time   : 0.000
% 2.62/2.79  #    Success case prop solver time     : 0.000
% 2.62/2.79  # Current number of processed clauses  : 198
% 2.62/2.79  #    Positive orientable unit clauses  : 39
% 2.62/2.79  #    Positive unorientable unit clauses: 1
% 2.62/2.79  #    Negative unit clauses             : 5
% 2.62/2.79  #    Non-unit-clauses                  : 153
% 2.62/2.79  # Current number of unprocessed clauses: 163339
% 2.62/2.79  # ...number of literals in the above   : 833401
% 2.62/2.79  # Current number of archived formulas  : 0
% 2.62/2.79  # Current number of archived clauses   : 4356
% 2.62/2.79  # Clause-clause subsumption calls (NU) : 2785184
% 2.62/2.79  # Rec. Clause-clause subsumption calls : 307410
% 2.62/2.79  # Non-unit clause-clause subsumptions  : 5321
% 2.62/2.79  # Unit Clause-clause subsumption calls : 12159
% 2.62/2.79  # Rewrite failures with RHS unbound    : 0
% 2.62/2.79  # BW rewrite match attempts            : 316
% 2.62/2.79  # BW rewrite match successes           : 50
% 2.62/2.79  # Condensation attempts                : 0
% 2.62/2.79  # Condensation successes               : 0
% 2.62/2.79  # Termbank termtop insertions          : 6797274
% 2.63/2.80  
% 2.63/2.80  # -------------------------------------------------
% 2.63/2.80  # User time                : 2.405 s
% 2.63/2.80  # System time              : 0.073 s
% 2.63/2.80  # Total time               : 2.478 s
% 2.63/2.80  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

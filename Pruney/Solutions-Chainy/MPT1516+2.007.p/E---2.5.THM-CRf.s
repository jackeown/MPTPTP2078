%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:06 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 161 expanded)
%              Number of clauses        :   40 (  67 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  513 (1238 expanded)
%              Number of equality atoms :   77 ( 157 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(c_0_14,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( ( ~ r4_lattice3(X36,X37,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r2_hidden(X39,X38)
        | r1_lattices(X36,X39,X37)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) )
      & ( m1_subset_1(esk7_3(X36,X37,X40),u1_struct_0(X36))
        | r4_lattice3(X36,X37,X40)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) )
      & ( r2_hidden(esk7_3(X36,X37,X40),X40)
        | r4_lattice3(X36,X37,X40)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) )
      & ( ~ r1_lattices(X36,esk7_3(X36,X37,X40),X37)
        | r4_lattice3(X36,X37,X40)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_19,plain,(
    ! [X49,X50,X51,X52] :
      ( ( r4_lattice3(X49,X51,X50)
        | X51 != k15_lattice3(X49,X50)
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49)
        | v2_struct_0(X49)
        | ~ l3_lattices(X49) )
      & ( ~ m1_subset_1(X52,u1_struct_0(X49))
        | ~ r4_lattice3(X49,X52,X50)
        | r1_lattices(X49,X51,X52)
        | X51 != k15_lattice3(X49,X50)
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49)
        | v2_struct_0(X49)
        | ~ l3_lattices(X49) )
      & ( m1_subset_1(esk11_3(X49,X50,X51),u1_struct_0(X49))
        | ~ r4_lattice3(X49,X51,X50)
        | X51 = k15_lattice3(X49,X50)
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49)
        | v2_struct_0(X49)
        | ~ l3_lattices(X49) )
      & ( r4_lattice3(X49,esk11_3(X49,X50,X51),X50)
        | ~ r4_lattice3(X49,X51,X50)
        | X51 = k15_lattice3(X49,X50)
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49)
        | v2_struct_0(X49)
        | ~ l3_lattices(X49) )
      & ( ~ r1_lattices(X49,X51,esk11_3(X49,X50,X51))
        | ~ r4_lattice3(X49,X51,X50)
        | X51 = k15_lattice3(X49,X50)
        | ~ m1_subset_1(X51,u1_struct_0(X49))
        | v2_struct_0(X49)
        | ~ v10_lattices(X49)
        | ~ v4_lattice3(X49)
        | ~ l3_lattices(X49)
        | v2_struct_0(X49)
        | ~ l3_lattices(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_20,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_lattices(X2,X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | X4 != k15_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r4_lattice3(X1,X2,k1_xboole_0)
    | v2_struct_0(X1)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_lattices(X15,X16,X17)
        | k1_lattices(X15,X16,X17) = X17
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) )
      & ( k1_lattices(X15,X16,X17) != X17
        | r1_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r4_lattice3(X1,X2,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X24] :
      ( ( l1_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( l2_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_28,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v9_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | k2_lattices(X18,X19,k1_lattices(X18,X19,X20)) = X19
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk2_1(X18),u1_struct_0(X18))
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk3_1(X18),u1_struct_0(X18))
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( k2_lattices(X18,esk2_1(X18),k1_lattices(X18,esk2_1(X18),esk3_1(X18))) != esk2_1(X18)
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_29,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,k1_xboole_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X10] :
      ( ( ~ v2_struct_0(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v4_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v5_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v6_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v7_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v9_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_33,plain,(
    ! [X11,X12,X13] :
      ( ( k2_lattices(X11,X12,X13) = X12
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | X12 != k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( k2_lattices(X11,X13,X12) = X12
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | X12 != k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))
        | X12 = k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( k2_lattices(X11,X12,esk1_2(X11,X12)) != X12
        | k2_lattices(X11,esk1_2(X11,X12),X12) != X12
        | X12 = k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_34,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,k1_xboole_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X25,X27,X28] :
      ( ( m1_subset_1(esk4_1(X25),u1_struct_0(X25))
        | ~ v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( k2_lattices(X25,esk4_1(X25),X27) = esk4_1(X25)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( k2_lattices(X25,X27,esk4_1(X25)) = esk4_1(X25)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( m1_subset_1(esk5_2(X25,X28),u1_struct_0(X25))
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( k2_lattices(X25,X28,esk5_2(X25,X28)) != X28
        | k2_lattices(X25,esk5_2(X25,X28),X28) != X28
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_38,plain,(
    ! [X54,X55,X56] :
      ( ( ~ v6_lattices(X54)
        | ~ m1_subset_1(X55,u1_struct_0(X54))
        | ~ m1_subset_1(X56,u1_struct_0(X54))
        | k2_lattices(X54,X55,X56) = k2_lattices(X54,X56,X55)
        | v2_struct_0(X54)
        | ~ l1_lattices(X54) )
      & ( m1_subset_1(esk12_1(X54),u1_struct_0(X54))
        | v6_lattices(X54)
        | v2_struct_0(X54)
        | ~ l1_lattices(X54) )
      & ( m1_subset_1(esk13_1(X54),u1_struct_0(X54))
        | v6_lattices(X54)
        | v2_struct_0(X54)
        | ~ l1_lattices(X54) )
      & ( k2_lattices(X54,esk12_1(X54),esk13_1(X54)) != k2_lattices(X54,esk13_1(X54),esk12_1(X54))
        | v6_lattices(X54)
        | v2_struct_0(X54)
        | ~ l1_lattices(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_39,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,k1_xboole_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_41,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_42,plain,(
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l1_lattices(X23)
      | m1_subset_1(k5_lattices(X23),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_43,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk5_2(X1,X2)) != X2
    | k2_lattices(X1,esk5_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,negated_conjecture,(
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

cnf(c_0_47,plain,
    ( X1 = X2
    | v2_struct_0(X3)
    | X1 != k15_lattice3(X3,k1_xboole_0)
    | X2 != k5_lattices(X3)
    | ~ v4_lattice3(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v13_lattices(X3)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X59,X60] :
      ( v2_struct_0(X59)
      | ~ l3_lattices(X59)
      | m1_subset_1(k15_lattice3(X59,X60),u1_struct_0(X59)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_50,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk5_2(X1,X2)) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_51,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk18_0)
    & v10_lattices(esk18_0)
    & v4_lattice3(esk18_0)
    & l3_lattices(esk18_0)
    & ( v2_struct_0(esk18_0)
      | ~ v10_lattices(esk18_0)
      | ~ v13_lattices(esk18_0)
      | ~ l3_lattices(esk18_0)
      | k5_lattices(esk18_0) != k15_lattice3(esk18_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_46])])])])).

cnf(c_0_53,plain,
    ( X1 = k5_lattices(X2)
    | v2_struct_0(X2)
    | X1 != k15_lattice3(X2,k1_xboole_0)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v13_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_41])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,k1_xboole_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_40]),c_0_51]),c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(esk18_0)
    | ~ v10_lattices(esk18_0)
    | ~ v13_lattices(esk18_0)
    | ~ l3_lattices(esk18_0)
    | k5_lattices(esk18_0) != k15_lattice3(esk18_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( l3_lattices(esk18_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( v10_lattices(esk18_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk18_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k15_lattice3(X1,X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | k15_lattice3(X1,X2) != k15_lattice3(X1,k1_xboole_0)
    | ~ v4_lattice3(X1)
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,k1_xboole_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( k15_lattice3(esk18_0,k1_xboole_0) != k5_lattices(esk18_0)
    | ~ v13_lattices(esk18_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_63,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( v4_lattice3(esk18_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k15_lattice3(X1,X2) != k15_lattice3(X1,k1_xboole_0)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( ~ v13_lattices(esk18_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_58]),c_0_57])]),c_0_59])).

cnf(c_0_67,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_64]),c_0_58]),c_0_57])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.033 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.20/0.46  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.46  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.46  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.46  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.20/0.46  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.46  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 0.20/0.46  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.46  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.20/0.46  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.20/0.46  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.20/0.46  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.20/0.46  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.20/0.46  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.46  fof(c_0_14, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.20/0.46  fof(c_0_15, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.46  cnf(c_0_16, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.46  cnf(c_0_17, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  fof(c_0_18, plain, ![X36, X37, X38, X39, X40]:((~r4_lattice3(X36,X37,X38)|(~m1_subset_1(X39,u1_struct_0(X36))|(~r2_hidden(X39,X38)|r1_lattices(X36,X39,X37)))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))&((m1_subset_1(esk7_3(X36,X37,X40),u1_struct_0(X36))|r4_lattice3(X36,X37,X40)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))&((r2_hidden(esk7_3(X36,X37,X40),X40)|r4_lattice3(X36,X37,X40)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))&(~r1_lattices(X36,esk7_3(X36,X37,X40),X37)|r4_lattice3(X36,X37,X40)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.46  fof(c_0_19, plain, ![X49, X50, X51, X52]:(((r4_lattice3(X49,X51,X50)|X51!=k15_lattice3(X49,X50)|~m1_subset_1(X51,u1_struct_0(X49))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49))|(v2_struct_0(X49)|~l3_lattices(X49)))&(~m1_subset_1(X52,u1_struct_0(X49))|(~r4_lattice3(X49,X52,X50)|r1_lattices(X49,X51,X52))|X51!=k15_lattice3(X49,X50)|~m1_subset_1(X51,u1_struct_0(X49))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49))|(v2_struct_0(X49)|~l3_lattices(X49))))&((m1_subset_1(esk11_3(X49,X50,X51),u1_struct_0(X49))|~r4_lattice3(X49,X51,X50)|X51=k15_lattice3(X49,X50)|~m1_subset_1(X51,u1_struct_0(X49))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49))|(v2_struct_0(X49)|~l3_lattices(X49)))&((r4_lattice3(X49,esk11_3(X49,X50,X51),X50)|~r4_lattice3(X49,X51,X50)|X51=k15_lattice3(X49,X50)|~m1_subset_1(X51,u1_struct_0(X49))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49))|(v2_struct_0(X49)|~l3_lattices(X49)))&(~r1_lattices(X49,X51,esk11_3(X49,X50,X51))|~r4_lattice3(X49,X51,X50)|X51=k15_lattice3(X49,X50)|~m1_subset_1(X51,u1_struct_0(X49))|(v2_struct_0(X49)|~v10_lattices(X49)|~v4_lattice3(X49)|~l3_lattices(X49))|(v2_struct_0(X49)|~l3_lattices(X49)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.46  cnf(c_0_20, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.46  cnf(c_0_21, plain, (r2_hidden(esk7_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_22, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_23, plain, (r4_lattice3(X1,X2,k1_xboole_0)|v2_struct_0(X1)|X3!=k1_xboole_0|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.46  fof(c_0_24, plain, ![X15, X16, X17]:((~r1_lattices(X15,X16,X17)|k1_lattices(X15,X16,X17)=X17|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l2_lattices(X15)))&(k1_lattices(X15,X16,X17)!=X17|r1_lattices(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l2_lattices(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.20/0.46  cnf(c_0_25, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_22])).
% 0.20/0.46  cnf(c_0_26, plain, (r4_lattice3(X1,X2,k1_xboole_0)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.46  fof(c_0_27, plain, ![X24]:((l1_lattices(X24)|~l3_lattices(X24))&(l2_lattices(X24)|~l3_lattices(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.46  fof(c_0_28, plain, ![X18, X19, X20]:((~v9_lattices(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~m1_subset_1(X20,u1_struct_0(X18))|k2_lattices(X18,X19,k1_lattices(X18,X19,X20))=X19))|(v2_struct_0(X18)|~l3_lattices(X18)))&((m1_subset_1(esk2_1(X18),u1_struct_0(X18))|v9_lattices(X18)|(v2_struct_0(X18)|~l3_lattices(X18)))&((m1_subset_1(esk3_1(X18),u1_struct_0(X18))|v9_lattices(X18)|(v2_struct_0(X18)|~l3_lattices(X18)))&(k2_lattices(X18,esk2_1(X18),k1_lattices(X18,esk2_1(X18),esk3_1(X18)))!=esk2_1(X18)|v9_lattices(X18)|(v2_struct_0(X18)|~l3_lattices(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.20/0.46  cnf(c_0_29, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_30, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|X2!=k15_lattice3(X1,k1_xboole_0)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.46  cnf(c_0_31, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.46  fof(c_0_32, plain, ![X10]:(((((((~v2_struct_0(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))&(v4_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v5_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v6_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v7_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v8_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v9_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.46  fof(c_0_33, plain, ![X11, X12, X13]:(((k2_lattices(X11,X12,X13)=X12|~m1_subset_1(X13,u1_struct_0(X11))|X12!=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11)))&(k2_lattices(X11,X13,X12)=X12|~m1_subset_1(X13,u1_struct_0(X11))|X12!=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11))))&((m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))|X12=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11)))&(k2_lattices(X11,X12,esk1_2(X11,X12))!=X12|k2_lattices(X11,esk1_2(X11,X12),X12)!=X12|X12=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.20/0.46  cnf(c_0_34, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.46  cnf(c_0_35, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|X2!=k15_lattice3(X1,k1_xboole_0)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.46  cnf(c_0_36, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  fof(c_0_37, plain, ![X25, X27, X28]:(((m1_subset_1(esk4_1(X25),u1_struct_0(X25))|~v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))&((k2_lattices(X25,esk4_1(X25),X27)=esk4_1(X25)|~m1_subset_1(X27,u1_struct_0(X25))|~v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))&(k2_lattices(X25,X27,esk4_1(X25))=esk4_1(X25)|~m1_subset_1(X27,u1_struct_0(X25))|~v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))))&((m1_subset_1(esk5_2(X25,X28),u1_struct_0(X25))|~m1_subset_1(X28,u1_struct_0(X25))|v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))&(k2_lattices(X25,X28,esk5_2(X25,X28))!=X28|k2_lattices(X25,esk5_2(X25,X28),X28)!=X28|~m1_subset_1(X28,u1_struct_0(X25))|v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.20/0.46  fof(c_0_38, plain, ![X54, X55, X56]:((~v6_lattices(X54)|(~m1_subset_1(X55,u1_struct_0(X54))|(~m1_subset_1(X56,u1_struct_0(X54))|k2_lattices(X54,X55,X56)=k2_lattices(X54,X56,X55)))|(v2_struct_0(X54)|~l1_lattices(X54)))&((m1_subset_1(esk12_1(X54),u1_struct_0(X54))|v6_lattices(X54)|(v2_struct_0(X54)|~l1_lattices(X54)))&((m1_subset_1(esk13_1(X54),u1_struct_0(X54))|v6_lattices(X54)|(v2_struct_0(X54)|~l1_lattices(X54)))&(k2_lattices(X54,esk12_1(X54),esk13_1(X54))!=k2_lattices(X54,esk13_1(X54),esk12_1(X54))|v6_lattices(X54)|(v2_struct_0(X54)|~l1_lattices(X54)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.20/0.46  cnf(c_0_39, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.46  cnf(c_0_40, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|X2!=k15_lattice3(X1,k1_xboole_0)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.20/0.46  cnf(c_0_41, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.46  fof(c_0_42, plain, ![X23]:(v2_struct_0(X23)|~l1_lattices(X23)|m1_subset_1(k5_lattices(X23),u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.20/0.46  cnf(c_0_43, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk5_2(X1,X2))!=X2|k2_lattices(X1,esk5_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  cnf(c_0_44, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.46  cnf(c_0_45, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  fof(c_0_46, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.20/0.46  cnf(c_0_47, plain, (X1=X2|v2_struct_0(X3)|X1!=k15_lattice3(X3,k1_xboole_0)|X2!=k5_lattices(X3)|~v4_lattice3(X3)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v13_lattices(X3)|~v10_lattices(X3)|~l3_lattices(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.46  cnf(c_0_48, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.46  fof(c_0_49, plain, ![X59, X60]:(v2_struct_0(X59)|~l3_lattices(X59)|m1_subset_1(k15_lattice3(X59,X60),u1_struct_0(X59))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.46  cnf(c_0_50, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk5_2(X1,X2))!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)|~v6_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.20/0.46  cnf(c_0_51, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  fof(c_0_52, negated_conjecture, ((((~v2_struct_0(esk18_0)&v10_lattices(esk18_0))&v4_lattice3(esk18_0))&l3_lattices(esk18_0))&(v2_struct_0(esk18_0)|~v10_lattices(esk18_0)|~v13_lattices(esk18_0)|~l3_lattices(esk18_0)|k5_lattices(esk18_0)!=k15_lattice3(esk18_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_46])])])])).
% 0.20/0.46  cnf(c_0_53, plain, (X1=k5_lattices(X2)|v2_struct_0(X2)|X1!=k15_lattice3(X2,k1_xboole_0)|~v4_lattice3(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v13_lattices(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_41])).
% 0.20/0.46  cnf(c_0_54, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.46  cnf(c_0_55, plain, (v13_lattices(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,k1_xboole_0)|~v4_lattice3(X1)|~m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_40]), c_0_51]), c_0_41])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (v2_struct_0(esk18_0)|~v10_lattices(esk18_0)|~v13_lattices(esk18_0)|~l3_lattices(esk18_0)|k5_lattices(esk18_0)!=k15_lattice3(esk18_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (l3_lattices(esk18_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.46  cnf(c_0_58, negated_conjecture, (v10_lattices(esk18_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk18_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.46  cnf(c_0_60, plain, (k15_lattice3(X1,X2)=k5_lattices(X1)|v2_struct_0(X1)|k15_lattice3(X1,X2)!=k15_lattice3(X1,k1_xboole_0)|~v4_lattice3(X1)|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.46  cnf(c_0_61, plain, (v13_lattices(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,k1_xboole_0)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_41])).
% 0.20/0.46  cnf(c_0_62, negated_conjecture, (k15_lattice3(esk18_0,k1_xboole_0)!=k5_lattices(esk18_0)|~v13_lattices(esk18_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])]), c_0_59])).
% 0.20/0.46  cnf(c_0_63, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_60])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (v4_lattice3(esk18_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.46  cnf(c_0_65, plain, (v13_lattices(X1)|v2_struct_0(X1)|k15_lattice3(X1,X2)!=k15_lattice3(X1,k1_xboole_0)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_61, c_0_54])).
% 0.20/0.46  cnf(c_0_66, negated_conjecture, (~v13_lattices(esk18_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_58]), c_0_57])]), c_0_59])).
% 0.20/0.46  cnf(c_0_67, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_65])).
% 0.20/0.46  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_64]), c_0_58]), c_0_57])]), c_0_59]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 69
% 0.20/0.46  # Proof object clause steps            : 40
% 0.20/0.46  # Proof object formula steps           : 29
% 0.20/0.46  # Proof object conjectures             : 11
% 0.20/0.46  # Proof object clause conjectures      : 8
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 21
% 0.20/0.46  # Proof object initial formulas used   : 14
% 0.20/0.46  # Proof object generating inferences   : 17
% 0.20/0.46  # Proof object simplifying inferences  : 23
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 20
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 73
% 0.20/0.46  # Removed in clause preprocessing      : 1
% 0.20/0.46  # Initial clauses in saturation        : 72
% 0.20/0.46  # Processed clauses                    : 805
% 0.20/0.46  # ...of these trivial                  : 9
% 0.20/0.46  # ...subsumed                          : 366
% 0.20/0.46  # ...remaining for further processing  : 430
% 0.20/0.46  # Other redundant clauses eliminated   : 5
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 47
% 0.20/0.46  # Backward-rewritten                   : 0
% 0.20/0.46  # Generated clauses                    : 1502
% 0.20/0.46  # ...of the previous two non-trivial   : 1289
% 0.20/0.46  # Contextual simplify-reflections      : 123
% 0.20/0.46  # Paramodulations                      : 1480
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 22
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 309
% 0.20/0.46  #    Positive orientable unit clauses  : 3
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 3
% 0.20/0.46  #    Non-unit-clauses                  : 303
% 0.20/0.46  # Current number of unprocessed clauses: 608
% 0.20/0.46  # ...number of literals in the above   : 6335
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 119
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 36353
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 946
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 535
% 0.20/0.46  # Unit Clause-clause subsumption calls : 135
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 0
% 0.20/0.46  # BW rewrite match successes           : 0
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 53011
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.120 s
% 0.20/0.46  # System time              : 0.005 s
% 0.20/0.46  # Total time               : 0.126 s
% 0.20/0.46  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

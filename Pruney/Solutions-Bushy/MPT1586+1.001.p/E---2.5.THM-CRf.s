%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1586+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:26 EST 2020

% Result     : Theorem 43.36s
% Output     : CNFRefutation 43.36s
% Verified   : 
% Statistics : Number of formulae       :  460 (11521147526490216448 expanded)
%              Number of clauses        :  435 (4358302571552151552 expanded)
%              Number of leaves         :   12 (2761156692019597824 expanded)
%              Depth                    :  202
%              Number of atoms          : 2131 (90495806573301055488 expanded)
%              Number of equality atoms :  553 (7693025869529694208 expanded)
%              Maximal formula depth    :   33 (   5 average)
%              Maximal clause size      :  107 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r1_yellow_0(X1,X3)
                  & r2_hidden(k1_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r1_yellow_0(X2,X3)
                  & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_yellow_0)).

fof(t62_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3,X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X2))
                 => ( X5 = X4
                   => ( ( r1_lattice3(X1,X3,X4)
                       => r1_lattice3(X2,X3,X5) )
                      & ( r2_lattice3(X1,X3,X4)
                       => r2_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_yellow_0)).

fof(t59_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(d7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) )
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_lattice3(X1,X2,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r2_lattice3(X1,X2,X5)
                           => r1_orders_2(X1,X4,X5) ) ) )
                   => X4 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

fof(t61_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X1,X3,X4)
                              & r2_hidden(X5,u1_struct_0(X2)) )
                           => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

fof(t63_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( X5 = X4
                       => ( ( r1_lattice3(X2,X3,X5)
                           => r1_lattice3(X1,X3,X4) )
                          & ( r2_lattice3(X2,X3,X5)
                           => r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_yellow_0)).

fof(t60_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X2,X5,X6) )
                           => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => ( ( r1_yellow_0(X1,X3)
                    & r2_hidden(k1_yellow_0(X1,X3),u1_struct_0(X2)) )
                 => ( r1_yellow_0(X2,X3)
                    & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_yellow_0])).

fof(c_0_13,plain,(
    ! [X50,X51,X52,X53,X54] :
      ( ( ~ r1_lattice3(X50,X52,X53)
        | r1_lattice3(X51,X52,X54)
        | X54 != X53
        | ~ m1_subset_1(X54,u1_struct_0(X51))
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | v2_struct_0(X51)
        | ~ v4_yellow_0(X51,X50)
        | ~ m1_yellow_0(X51,X50)
        | v2_struct_0(X50)
        | ~ l1_orders_2(X50) )
      & ( ~ r2_lattice3(X50,X52,X53)
        | r2_lattice3(X51,X52,X54)
        | X54 != X53
        | ~ m1_subset_1(X54,u1_struct_0(X51))
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | v2_struct_0(X51)
        | ~ v4_yellow_0(X51,X50)
        | ~ m1_yellow_0(X51,X50)
        | v2_struct_0(X50)
        | ~ l1_orders_2(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_yellow_0])])])])])).

fof(c_0_14,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ l1_orders_2(X35)
      | v2_struct_0(X36)
      | ~ m1_yellow_0(X36,X35)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | m1_subset_1(X37,u1_struct_0(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_yellow_0])])])])).

fof(c_0_15,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | m1_subset_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & v4_yellow_0(esk7_0,esk6_0)
    & m1_yellow_0(esk7_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & r1_yellow_0(esk6_0,esk8_0)
    & r2_hidden(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk7_0))
    & ( ~ r1_yellow_0(esk7_0,esk8_0)
      | k1_yellow_0(esk7_0,esk8_0) != k1_yellow_0(esk6_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_17,plain,
    ( r2_lattice3(X4,X2,X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,X3)
    | X5 != X3
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_yellow_0(X4,X1)
    | ~ m1_yellow_0(X4,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_lattice3(X18,X19,X20)
        | X20 != k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r2_lattice3(X18,X19,X21)
        | r1_orders_2(X18,X20,X21)
        | X20 != k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk5_3(X18,X19,X20),u1_struct_0(X18))
        | ~ r2_lattice3(X18,X19,X20)
        | X20 = k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( r2_lattice3(X18,X19,esk5_3(X18,X19,X20))
        | ~ r2_lattice3(X18,X19,X20)
        | X20 = k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ r1_orders_2(X18,X20,esk5_3(X18,X19,X20))
        | ~ r2_lattice3(X18,X19,X20)
        | X20 = k1_yellow_0(X18,X19)
        | ~ r1_yellow_0(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_22,plain,(
    ! [X23,X24] :
      ( ~ l1_orders_2(X23)
      | m1_subset_1(k1_yellow_0(X23,X24),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_23,plain,(
    ! [X25,X26] :
      ( ~ l1_orders_2(X25)
      | ~ m1_yellow_0(X26,X25)
      | l1_orders_2(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_lattice3(X1,X3,X4)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ r2_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X7,X8,X10,X11,X13,X14,X17] :
      ( ( m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | ~ r1_yellow_0(X7,X8)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X8,esk1_2(X7,X8))
        | ~ r1_yellow_0(X7,X8)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X8,X10)
        | r1_orders_2(X7,esk1_2(X7,X8),X10)
        | ~ r1_yellow_0(X7,X8)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_3(X7,X8,X11),u1_struct_0(X7))
        | ~ r2_lattice3(X7,X8,X11)
        | X11 = esk1_2(X7,X8)
        | ~ m1_subset_1(X11,u1_struct_0(X7))
        | ~ r1_yellow_0(X7,X8)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X8,esk2_3(X7,X8,X11))
        | ~ r2_lattice3(X7,X8,X11)
        | X11 = esk1_2(X7,X8)
        | ~ m1_subset_1(X11,u1_struct_0(X7))
        | ~ r1_yellow_0(X7,X8)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X11,esk2_3(X7,X8,X11))
        | ~ r2_lattice3(X7,X8,X11)
        | X11 = esk1_2(X7,X8)
        | ~ m1_subset_1(X11,u1_struct_0(X7))
        | ~ r1_yellow_0(X7,X8)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk4_3(X7,X13,X14),u1_struct_0(X7))
        | m1_subset_1(esk3_3(X7,X13,X14),u1_struct_0(X7))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X13,esk4_3(X7,X13,X14))
        | m1_subset_1(esk3_3(X7,X13,X14),u1_struct_0(X7))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X17)
        | r1_orders_2(X7,esk4_3(X7,X13,X14),X17)
        | m1_subset_1(esk3_3(X7,X13,X14),u1_struct_0(X7))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( esk4_3(X7,X13,X14) != X14
        | m1_subset_1(esk3_3(X7,X13,X14),u1_struct_0(X7))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk4_3(X7,X13,X14),u1_struct_0(X7))
        | r2_lattice3(X7,X13,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X13,esk4_3(X7,X13,X14))
        | r2_lattice3(X7,X13,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X17)
        | r1_orders_2(X7,esk4_3(X7,X13,X14),X17)
        | r2_lattice3(X7,X13,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( esk4_3(X7,X13,X14) != X14
        | r2_lattice3(X7,X13,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk4_3(X7,X13,X14),u1_struct_0(X7))
        | ~ r1_orders_2(X7,X14,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X13,esk4_3(X7,X13,X14))
        | ~ r1_orders_2(X7,X14,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X17)
        | r1_orders_2(X7,esk4_3(X7,X13,X14),X17)
        | ~ r1_orders_2(X7,X14,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) )
      & ( esk4_3(X7,X13,X14) != X14
        | ~ r1_orders_2(X7,X14,esk3_3(X7,X13,X14))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X13,X14)
        | r1_yellow_0(X7,X13)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_yellow_0])])])])])])).

cnf(c_0_30,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_yellow_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_lattice3(esk7_0,X2,k1_yellow_0(esk6_0,esk8_0))
    | ~ v4_yellow_0(esk7_0,X1)
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(X1,X2,k1_yellow_0(esk6_0,esk8_0))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v4_yellow_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r1_yellow_0(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r2_lattice3(esk6_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_45,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ~ l1_orders_2(X44)
      | ~ v4_yellow_0(X45,X44)
      | ~ m1_yellow_0(X45,X44)
      | ~ m1_subset_1(X46,u1_struct_0(X44))
      | ~ m1_subset_1(X47,u1_struct_0(X44))
      | ~ m1_subset_1(X48,u1_struct_0(X45))
      | ~ m1_subset_1(X49,u1_struct_0(X45))
      | X48 != X46
      | X49 != X47
      | ~ r1_orders_2(X44,X46,X47)
      | ~ r2_hidden(X48,u1_struct_0(X45))
      | r1_orders_2(X45,X48,X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_yellow_0])])])).

cnf(c_0_46,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_39])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( r1_orders_2(X2,X5,X6)
    | ~ l1_orders_2(X1)
    | ~ v4_yellow_0(X2,X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X5 != X3
    | X6 != X4
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r2_hidden(X5,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_49,plain,(
    ! [X55,X56,X57,X58,X59] :
      ( ( ~ r1_lattice3(X56,X57,X59)
        | r1_lattice3(X55,X57,X58)
        | X59 != X58
        | ~ m1_subset_1(X59,u1_struct_0(X56))
        | ~ m1_subset_1(X58,u1_struct_0(X55))
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | v2_struct_0(X56)
        | ~ m1_yellow_0(X56,X55)
        | v2_struct_0(X55)
        | ~ l1_orders_2(X55) )
      & ( ~ r2_lattice3(X56,X57,X59)
        | r2_lattice3(X55,X57,X58)
        | X59 != X58
        | ~ m1_subset_1(X59,u1_struct_0(X56))
        | ~ m1_subset_1(X58,u1_struct_0(X55))
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | v2_struct_0(X56)
        | ~ m1_yellow_0(X56,X55)
        | v2_struct_0(X55)
        | ~ l1_orders_2(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t63_yellow_0])])])])])).

cnf(c_0_50,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_44])])).

cnf(c_0_51,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ v4_yellow_0(X1,X4)
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X4)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_48,c_0_19])])])).

cnf(c_0_52,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,plain,
    ( r2_lattice3(X4,X2,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ r2_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_yellow_0(X1,X4)
    | ~ l1_orders_2(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_50]),c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),X1)
    | ~ v4_yellow_0(esk7_0,X2)
    | ~ m1_yellow_0(esk7_0,X2)
    | ~ r1_orders_2(X2,k1_yellow_0(esk6_0,esk8_0),X1)
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_25]),c_0_39])])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_lattice3(X1,X3,X4)
    | ~ m1_yellow_0(X2,X1)
    | ~ r2_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_18])).

cnf(c_0_60,plain,
    ( r2_lattice3(X1,X2,esk5_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_61,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),X1)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_34]),c_0_31]),c_0_57]),c_0_32])])).

cnf(c_0_64,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_47]),c_0_44])])).

cnf(c_0_65,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_26])).

cnf(c_0_66,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,X1,esk5_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_25]),c_0_39])])).

cnf(c_0_67,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_32])])).

cnf(c_0_68,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_50]),c_0_62]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_71,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_47]),c_0_44])])).

cnf(c_0_72,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_37]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_74,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_75,plain,(
    ! [X38,X39,X40,X41,X42,X43] :
      ( ~ l1_orders_2(X38)
      | ~ m1_yellow_0(X39,X38)
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | ~ m1_subset_1(X41,u1_struct_0(X38))
      | ~ m1_subset_1(X42,u1_struct_0(X39))
      | ~ m1_subset_1(X43,u1_struct_0(X39))
      | X42 != X40
      | X43 != X41
      | ~ r1_orders_2(X39,X42,X43)
      | r1_orders_2(X38,X40,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_yellow_0])])])).

cnf(c_0_76,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_73]),c_0_26])).

cnf(c_0_77,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_73]),c_0_26])).

cnf(c_0_78,negated_conjecture,
    ( r2_lattice3(esk7_0,X1,esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_25]),c_0_39])])).

cnf(c_0_79,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X5 != X3
    | X6 != X4
    | ~ r1_orders_2(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_81,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_82,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_44])).

cnf(c_0_83,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ m1_yellow_0(X4,X1)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_79])])).

cnf(c_0_84,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_80]),c_0_32])])).

cnf(c_0_85,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_82]),c_0_44])])).

cnf(c_0_87,negated_conjecture,
    ( r1_orders_2(X1,X2,k1_yellow_0(esk6_0,esk8_0))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r1_orders_2(esk7_0,X2,k1_yellow_0(esk6_0,esk8_0))
    | ~ m1_subset_1(k1_yellow_0(esk6_0,esk8_0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_25])).

cnf(c_0_88,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | m1_subset_1(esk3_3(X2,X3,X4),u1_struct_0(X2))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_89,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_37])).

cnf(c_0_90,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_80]),c_0_32])])).

fof(c_0_92,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ v4_orders_2(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ m1_subset_1(X32,u1_struct_0(X29))
      | ~ r1_orders_2(X29,X30,X31)
      | ~ r1_orders_2(X29,X31,X32)
      | r1_orders_2(X29,X30,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_orders_2(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_31]),c_0_57]),c_0_32])])).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),X2)
    | m1_subset_1(esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r2_lattice3(esk7_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_25]),c_0_39])])).

cnf(c_0_95,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_37])).

cnf(c_0_97,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_80]),c_0_32])])).

cnf(c_0_98,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_100,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_73]),c_0_80])).

cnf(c_0_101,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_44]),c_0_44]),c_0_25])])).

cnf(c_0_102,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_95]),c_0_32])])).

cnf(c_0_103,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_90])).

cnf(c_0_104,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_37])).

cnf(c_0_105,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,X2,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_95]),c_0_99]),c_0_32])])).

cnf(c_0_106,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_37]),c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_90])).

cnf(c_0_109,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_57])]),c_0_80]),c_0_107]),c_0_108])).

cnf(c_0_110,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_109]),c_0_44])])).

cnf(c_0_111,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_110]),c_0_26])).

cnf(c_0_112,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_110]),c_0_26])).

cnf(c_0_113,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_114,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_115,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_113]),c_0_32])])).

cnf(c_0_116,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_70])).

cnf(c_0_117,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_82]),c_0_44])])).

cnf(c_0_118,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_37])).

cnf(c_0_119,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_110]),c_0_113])).

cnf(c_0_121,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_82]),c_0_44])])).

cnf(c_0_123,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])).

cnf(c_0_124,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_123])).

cnf(c_0_125,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_124])).

cnf(c_0_126,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_125]),c_0_32])])).

cnf(c_0_127,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,X2,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_125]),c_0_99]),c_0_32])])).

cnf(c_0_129,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_37]),c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_106]),c_0_57])]),c_0_80]),c_0_129]),c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_131]),c_0_44])])).

cnf(c_0_133,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_133])).

cnf(c_0_135,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_131]),c_0_44])])).

cnf(c_0_136,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_134]),c_0_135])).

cnf(c_0_137,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_138,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_136]),c_0_26])).

cnf(c_0_139,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_136]),c_0_26])).

cnf(c_0_140,negated_conjecture,
    ( r2_lattice3(esk7_0,X1,esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_25]),c_0_39])])).

cnf(c_0_141,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_142,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_143,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_44])).

cnf(c_0_144,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_141]),c_0_32])])).

cnf(c_0_145,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_70])).

cnf(c_0_146,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_143]),c_0_44])])).

cnf(c_0_147,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_148,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_144,c_0_37])).

cnf(c_0_149,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,X1)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_25]),c_0_39])])).

cnf(c_0_151,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_136]),c_0_141])).

cnf(c_0_152,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_153,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_150,c_0_44])).

cnf(c_0_154,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_155,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_153,c_0_154])).

cnf(c_0_156,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_155]),c_0_44])])).

cnf(c_0_157,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_156]),c_0_26])).

cnf(c_0_158,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_156]),c_0_26])).

cnf(c_0_159,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_160,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_161,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_159]),c_0_32])])).

cnf(c_0_162,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_160,c_0_70])).

cnf(c_0_163,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_143]),c_0_44])])).

cnf(c_0_164,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_161,c_0_37])).

cnf(c_0_165,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_166,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_156]),c_0_159])).

cnf(c_0_167,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_168,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_143]),c_0_44])])).

cnf(c_0_169,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_168])).

cnf(c_0_170,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_169])).

cnf(c_0_171,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_170])).

cnf(c_0_172,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_151,c_0_171])).

cnf(c_0_173,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_153,c_0_172])).

cnf(c_0_174,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_173]),c_0_44])])).

cnf(c_0_175,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_162,c_0_174])).

cnf(c_0_176,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_164,c_0_175])).

cnf(c_0_177,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_173]),c_0_44])])).

cnf(c_0_178,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_176]),c_0_177])).

cnf(c_0_179,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_180,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_178]),c_0_26])).

cnf(c_0_181,negated_conjecture,
    ( r2_lattice3(esk7_0,X1,esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,X1,esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_25]),c_0_39])])).

cnf(c_0_182,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_178]),c_0_26])).

cnf(c_0_183,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_184,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_181,c_0_44])).

cnf(c_0_185,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_186,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_183,c_0_70])).

cnf(c_0_187,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_184]),c_0_44])])).

cnf(c_0_188,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_185]),c_0_32])])).

cnf(c_0_189,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_186,c_0_187])).

cnf(c_0_190,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_188,c_0_37])).

cnf(c_0_191,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_189])).

cnf(c_0_192,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_193,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_190,c_0_191])).

cnf(c_0_194,negated_conjecture,
    ( r2_lattice3(esk7_0,X1,esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,X1)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_25]),c_0_39])])).

cnf(c_0_195,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_193])).

cnf(c_0_196,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_194,c_0_44])).

cnf(c_0_197,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_151,c_0_195])).

cnf(c_0_198,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r2_lattice3(X2,X3,esk3_3(X2,X3,X4))
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_199,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_196,c_0_197])).

cnf(c_0_200,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),X2)
    | r2_lattice3(esk7_0,X1,esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r2_lattice3(esk7_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_25]),c_0_39])])).

cnf(c_0_201,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_199]),c_0_44])])).

cnf(c_0_202,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r2_lattice3(esk7_0,X1,esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_200,c_0_25])).

cnf(c_0_203,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_201]),c_0_190])).

cnf(c_0_204,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_185]),c_0_32])])).

cnf(c_0_205,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_178]),c_0_185])).

cnf(c_0_206,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_202,c_0_44])).

cnf(c_0_207,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_203]),c_0_32])])).

cnf(c_0_208,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_204,c_0_37])).

cnf(c_0_209,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_185]),c_0_32])])).

cnf(c_0_210,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,X2,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_203]),c_0_99]),c_0_32])])).

cnf(c_0_211,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_205,c_0_206])).

cnf(c_0_212,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_207,c_0_37])).

cnf(c_0_213,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_208,c_0_191])).

cnf(c_0_214,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(esk7_0,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ v4_yellow_0(esk7_0,X1)
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(X1,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_136]),c_0_26])).

cnf(c_0_215,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_209,c_0_37])).

cnf(c_0_216,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_211]),c_0_57])]),c_0_185])).

cnf(c_0_217,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_212,c_0_213])).

cnf(c_0_218,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214,c_0_34]),c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_219,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_215,c_0_191])).

cnf(c_0_220,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_217]),c_0_218])).

cnf(c_0_221,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_219,c_0_220]),c_0_145])).

cnf(c_0_222,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_221]),c_0_44])])).

cnf(c_0_223,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_222])).

cnf(c_0_224,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_151,c_0_223])).

cnf(c_0_225,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,esk3_3(X2,X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_226,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_196,c_0_224])).

cnf(c_0_227,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)),X2)
    | r1_yellow_0(esk7_0,X1)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r2_lattice3(esk7_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_225,c_0_25]),c_0_39])])).

cnf(c_0_228,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_226]),c_0_44])])).

cnf(c_0_229,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r1_yellow_0(esk7_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_227,c_0_44]),c_0_44]),c_0_25])])).

cnf(c_0_230,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_186,c_0_228])).

cnf(c_0_231,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_229,c_0_224])).

cnf(c_0_232,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_208,c_0_230])).

cnf(c_0_233,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_205,c_0_231])).

cnf(c_0_234,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_212,c_0_232])).

cnf(c_0_235,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_215,c_0_230])).

cnf(c_0_236,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_233]),c_0_57])]),c_0_185]),c_0_234]),c_0_235])).

cnf(c_0_237,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_236]),c_0_44])])).

cnf(c_0_238,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_237]),c_0_26])).

cnf(c_0_239,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_237]),c_0_26])).

cnf(c_0_240,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_238,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_241,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_239,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_242,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_240]),c_0_32])])).

cnf(c_0_243,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_241,c_0_70])).

cnf(c_0_244,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_184]),c_0_44])])).

cnf(c_0_245,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_242,c_0_37])).

cnf(c_0_246,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_243,c_0_244])).

cnf(c_0_247,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_237]),c_0_240])).

cnf(c_0_248,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_245,c_0_246])).

cnf(c_0_249,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_184]),c_0_44])])).

cnf(c_0_250,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_248]),c_0_249])).

cnf(c_0_251,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_186,c_0_250])).

cnf(c_0_252,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_145,c_0_251])).

cnf(c_0_253,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_190,c_0_252])).

cnf(c_0_254,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_253])).

cnf(c_0_255,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_151,c_0_254])).

cnf(c_0_256,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_196,c_0_255])).

cnf(c_0_257,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_256]),c_0_44])])).

cnf(c_0_258,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_243,c_0_257])).

cnf(c_0_259,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_245,c_0_258])).

cnf(c_0_260,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_256]),c_0_44])])).

cnf(c_0_261,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_259]),c_0_260])).

cnf(c_0_262,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_261]),c_0_190])).

cnf(c_0_263,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X2,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_262]),c_0_99]),c_0_32])])).

cnf(c_0_264,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X2),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,k1_yellow_0(esk6_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_263,c_0_57])).

cnf(c_0_265,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_262]),c_0_32])])).

cnf(c_0_266,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_264,c_0_185])).

cnf(c_0_267,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_265,c_0_37])).

cnf(c_0_268,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_208,c_0_252])).

cnf(c_0_269,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_266,c_0_211])).

cnf(c_0_270,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_267,c_0_268])).

cnf(c_0_271,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_215,c_0_252])).

cnf(c_0_272,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_269,c_0_270]),c_0_218])).

cnf(c_0_273,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_271,c_0_272]),c_0_145])).

cnf(c_0_274,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_273]),c_0_44])])).

cnf(c_0_275,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_243,c_0_274])).

cnf(c_0_276,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_245,c_0_275])).

cnf(c_0_277,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_273]),c_0_44])])).

cnf(c_0_278,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_276]),c_0_277])).

cnf(c_0_279,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_148,c_0_278])).

cnf(c_0_280,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_151,c_0_279])).

cnf(c_0_281,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_196,c_0_280])).

cnf(c_0_282,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_281]),c_0_44])])).

cnf(c_0_283,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_243,c_0_282])).

cnf(c_0_284,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_245,c_0_283])).

cnf(c_0_285,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_281]),c_0_44])])).

cnf(c_0_286,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_284]),c_0_285])).

cnf(c_0_287,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_186,c_0_286])).

cnf(c_0_288,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_229,c_0_280])).

cnf(c_0_289,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_208,c_0_287])).

cnf(c_0_290,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_205,c_0_288])).

cnf(c_0_291,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_267,c_0_289])).

cnf(c_0_292,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_215,c_0_287])).

cnf(c_0_293,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_266,c_0_290]),c_0_291]),c_0_292])).

cnf(c_0_294,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_293]),c_0_44])])).

cnf(c_0_295,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_243,c_0_294])).

cnf(c_0_296,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_39])).

cnf(c_0_297,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_245,c_0_295])).

cnf(c_0_298,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_293]),c_0_44])])).

cnf(c_0_299,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_yellow_0(esk7_0,X2),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_296]),c_0_26])).

cnf(c_0_300,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_lattice3(X1,X2,k1_yellow_0(esk7_0,X3))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,k1_yellow_0(esk7_0,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_296]),c_0_26])).

cnf(c_0_301,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_302,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_297]),c_0_298])).

cnf(c_0_303,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk7_0,X1),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_299,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_304,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,k1_yellow_0(esk7_0,X2))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk7_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_300,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_305,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301,c_0_302]),c_0_44]),c_0_25]),c_0_39])])).

cnf(c_0_306,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,X2)
    | m1_subset_1(esk5_3(esk6_0,X2,k1_yellow_0(esk7_0,X1)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X2,k1_yellow_0(esk7_0,X1))
    | ~ r1_yellow_0(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_303]),c_0_32])])).

cnf(c_0_307,negated_conjecture,
    ( r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk7_0,X1))
    | ~ r2_lattice3(esk7_0,esk8_0,k1_yellow_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_304,c_0_70])).

cnf(c_0_308,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,k1_yellow_0(esk7_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_305]),c_0_39])])).

cnf(c_0_309,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,X1)),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_306,c_0_37])).

cnf(c_0_310,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_307,c_0_308])).

cnf(c_0_311,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,X2)
    | r2_lattice3(esk6_0,X2,esk5_3(esk6_0,X2,k1_yellow_0(esk7_0,X1)))
    | ~ r2_lattice3(esk6_0,X2,k1_yellow_0(esk7_0,X1))
    | ~ r1_yellow_0(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_303]),c_0_32])])).

cnf(c_0_312,negated_conjecture,
    ( r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),k1_yellow_0(esk6_0,esk8_0))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_yellow_0(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_25]),c_0_39])])).

cnf(c_0_313,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_309,c_0_310])).

cnf(c_0_314,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,X1)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_311,c_0_37])).

cnf(c_0_315,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,X2)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk7_0,X1),esk5_3(esk6_0,X2,k1_yellow_0(esk7_0,X1)))
    | ~ r2_lattice3(esk6_0,X2,k1_yellow_0(esk7_0,X1))
    | ~ r1_yellow_0(esk6_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_303]),c_0_32])])).

cnf(c_0_316,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk7_0,X1),k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),k1_yellow_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_296]),c_0_303])])).

cnf(c_0_317,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk7_0,esk8_0),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_312,c_0_305]),c_0_44])])).

cnf(c_0_318,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_313]),c_0_32])])).

cnf(c_0_319,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_314,c_0_310])).

cnf(c_0_320,negated_conjecture,
    ( k1_yellow_0(esk7_0,X1) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk7_0,X1),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,X1)))
    | ~ r2_lattice3(esk6_0,esk8_0,k1_yellow_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_315,c_0_37])).

cnf(c_0_321,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,X2,esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_313]),c_0_99]),c_0_32])])).

cnf(c_0_322,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk7_0,esk8_0),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_316,c_0_317])).

cnf(c_0_323,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_318,c_0_37]),c_0_319])).

cnf(c_0_324,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk7_0,esk8_0),esk5_3(esk6_0,esk8_0,k1_yellow_0(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_320,c_0_310])).

cnf(c_0_325,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_321,c_0_322]),c_0_57]),c_0_303])]),c_0_323]),c_0_324])).

cnf(c_0_326,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_325]),c_0_26])).

cnf(c_0_327,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_325]),c_0_26])).

cnf(c_0_328,plain,
    ( r2_lattice3(X1,X2,esk3_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_329,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_326,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_330,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_327,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_331,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_328,c_0_302]),c_0_44]),c_0_25]),c_0_39])])).

cnf(c_0_332,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_329]),c_0_32])])).

cnf(c_0_333,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_330,c_0_70])).

cnf(c_0_334,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_331]),c_0_44])])).

cnf(c_0_335,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_332,c_0_37])).

cnf(c_0_336,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_333,c_0_334])).

cnf(c_0_337,plain,
    ( r1_yellow_0(X1,X2)
    | esk4_3(X1,X2,X3) != X3
    | ~ r1_orders_2(X1,X3,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_338,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_325]),c_0_329])).

cnf(c_0_339,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_335,c_0_336])).

cnf(c_0_340,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_yellow_0(esk7_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_337,c_0_302]),c_0_44]),c_0_25]),c_0_39])])).

cnf(c_0_341,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_338,c_0_339])).

cnf(c_0_342,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_340,c_0_341])).

cnf(c_0_343,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_342]),c_0_44])])).

cnf(c_0_344,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_343]),c_0_26])).

cnf(c_0_345,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_343]),c_0_26])).

cnf(c_0_346,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_344,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_347,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_345,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_348,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_346]),c_0_32])])).

cnf(c_0_349,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_347,c_0_70])).

cnf(c_0_350,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_331]),c_0_44])])).

cnf(c_0_351,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_348,c_0_37])).

cnf(c_0_352,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_349,c_0_350])).

cnf(c_0_353,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_343]),c_0_346])).

cnf(c_0_354,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_351,c_0_352])).

cnf(c_0_355,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_331]),c_0_44])])).

cnf(c_0_356,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_353,c_0_354]),c_0_355])).

cnf(c_0_357,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_333,c_0_356])).

cnf(c_0_358,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_335,c_0_357])).

cnf(c_0_359,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_338,c_0_358])).

cnf(c_0_360,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_yellow_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_340,c_0_359])).

cnf(c_0_361,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_360]),c_0_44])])).

cnf(c_0_362,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_349,c_0_361])).

cnf(c_0_363,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_351,c_0_362])).

cnf(c_0_364,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_360]),c_0_44])])).

cnf(c_0_365,negated_conjecture,
    ( ~ r1_yellow_0(esk7_0,esk8_0)
    | k1_yellow_0(esk7_0,esk8_0) != k1_yellow_0(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_366,negated_conjecture,
    ( k1_yellow_0(esk7_0,esk8_0) = k1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_353,c_0_363]),c_0_364])).

cnf(c_0_367,negated_conjecture,
    ( ~ r1_yellow_0(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_365,c_0_366])])).

cnf(c_0_368,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_47,c_0_367])).

cnf(c_0_369,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_368]),c_0_26])).

cnf(c_0_370,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_368]),c_0_26])).

cnf(c_0_371,negated_conjecture,
    ( m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_369,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_372,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk7_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_370,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_373,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_82,c_0_367])).

cnf(c_0_374,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_371]),c_0_32])])).

cnf(c_0_375,negated_conjecture,
    ( r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_372,c_0_70]),c_0_373])).

cnf(c_0_376,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_374,c_0_37]),c_0_375])).

cnf(c_0_377,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_371]),c_0_32])])).

cnf(c_0_378,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_101,c_0_367])).

cnf(c_0_379,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_376]),c_0_32])])).

cnf(c_0_380,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_377,c_0_37]),c_0_375])).

cnf(c_0_381,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_371]),c_0_32])])).

cnf(c_0_382,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,X2,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_376]),c_0_99]),c_0_32])])).

cnf(c_0_383,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_368]),c_0_371]),c_0_378])).

cnf(c_0_384,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_379,c_0_37]),c_0_380])).

cnf(c_0_385,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_381,c_0_37]),c_0_375])).

cnf(c_0_386,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_382,c_0_383]),c_0_57])]),c_0_371]),c_0_384]),c_0_385])).

cnf(c_0_387,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_386]),c_0_26])).

cnf(c_0_388,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_386]),c_0_26])).

cnf(c_0_389,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_387,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_390,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_388,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_391,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_389]),c_0_32])])).

cnf(c_0_392,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_390,c_0_70])).

cnf(c_0_393,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_143,c_0_367])).

cnf(c_0_394,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_391,c_0_37])).

cnf(c_0_395,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_392,c_0_393])).

cnf(c_0_396,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_386]),c_0_389])).

cnf(c_0_397,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_394,c_0_395])).

cnf(c_0_398,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_396,c_0_397])).

cnf(c_0_399,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_398]),c_0_367])).

cnf(c_0_400,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_399]),c_0_26])).

cnf(c_0_401,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_399]),c_0_26])).

cnf(c_0_402,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_400,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_403,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_401,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_404,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_402,c_0_70])).

cnf(c_0_405,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[c_0_184,c_0_367])).

cnf(c_0_406,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | m1_subset_1(esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_403]),c_0_32])])).

cnf(c_0_407,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_404,c_0_405])).

cnf(c_0_408,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_406,c_0_37])).

cnf(c_0_409,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_392,c_0_407])).

cnf(c_0_410,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_408,c_0_409])).

cnf(c_0_411,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_394,c_0_410])).

cnf(c_0_412,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_396,c_0_411])).

cnf(c_0_413,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_412]),c_0_367])).

cnf(c_0_414,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | m1_subset_1(esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_404,c_0_413]),c_0_408])).

cnf(c_0_415,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X2,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_414]),c_0_99]),c_0_32])])).

cnf(c_0_416,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | r2_lattice3(esk6_0,X1,esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_403]),c_0_32])])).

cnf(c_0_417,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X2),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,X1,k1_yellow_0(esk6_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_415,c_0_57])).

cnf(c_0_418,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_399]),c_0_403])).

cnf(c_0_419,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[c_0_206,c_0_367])).

cnf(c_0_420,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_414]),c_0_32])])).

cnf(c_0_421,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_416,c_0_37])).

cnf(c_0_422,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,X1)
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,X1,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_403]),c_0_32])])).

cnf(c_0_423,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_417,c_0_403])).

cnf(c_0_424,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_418,c_0_419])).

cnf(c_0_425,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_420,c_0_37])).

cnf(c_0_426,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_421,c_0_409])).

cnf(c_0_427,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | v2_struct_0(X1)
    | r2_lattice3(esk7_0,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ v4_yellow_0(esk7_0,X1)
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(X1,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_386]),c_0_26])).

cnf(c_0_428,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | ~ r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_422,c_0_37])).

cnf(c_0_429,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_423,c_0_424])).

cnf(c_0_430,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_425,c_0_426])).

cnf(c_0_431,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_427,c_0_34]),c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_432,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_428,c_0_409])).

cnf(c_0_433,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))))
    | r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_429,c_0_430]),c_0_431])).

cnf(c_0_434,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_432,c_0_433]),c_0_392])).

cnf(c_0_435,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_394,c_0_434])).

cnf(c_0_436,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,X1,k1_yellow_0(esk7_0,X2)),X3)
    | r1_yellow_0(esk7_0,X1)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X2),esk3_3(esk7_0,X1,k1_yellow_0(esk7_0,X2)))
    | ~ r2_lattice3(esk7_0,X1,k1_yellow_0(esk7_0,X2))
    | ~ r2_lattice3(esk7_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_225,c_0_296]),c_0_39])])).

cnf(c_0_437,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_396,c_0_435])).

cnf(c_0_438,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk7_0,X1)),k1_yellow_0(esk6_0,esk8_0))
    | r1_yellow_0(esk7_0,esk8_0)
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk7_0,X1),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk7_0,X1)))
    | ~ r2_lattice3(esk7_0,esk8_0,k1_yellow_0(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_436,c_0_44]),c_0_25])])).

cnf(c_0_439,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk7_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_437]),c_0_367])).

cnf(c_0_440,negated_conjecture,
    ( r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0))
    | ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_438,c_0_366]),c_0_44])]),c_0_367])).

cnf(c_0_441,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_404,c_0_439])).

cnf(c_0_442,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk7_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_440,c_0_437])).

cnf(c_0_443,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r2_lattice3(esk6_0,esk8_0,esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_421,c_0_441])).

cnf(c_0_444,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),k1_yellow_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_418,c_0_442])).

cnf(c_0_445,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_425,c_0_443])).

cnf(c_0_446,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0)
    | ~ r1_orders_2(esk6_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),esk5_3(esk6_0,esk8_0,esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_428,c_0_441])).

cnf(c_0_447,negated_conjecture,
    ( esk4_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)) = k1_yellow_0(esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_423,c_0_444]),c_0_445]),c_0_446])).

cnf(c_0_448,negated_conjecture,
    ( m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301,c_0_447]),c_0_44]),c_0_25]),c_0_39])]),c_0_367])).

cnf(c_0_449,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(X1))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_448]),c_0_26])).

cnf(c_0_450,negated_conjecture,
    ( ~ r1_orders_2(esk7_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_337,c_0_447]),c_0_44]),c_0_25]),c_0_39])]),c_0_367])).

cnf(c_0_451,negated_conjecture,
    ( m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_449,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_452,negated_conjecture,
    ( ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_448]),c_0_450])).

cnf(c_0_453,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_lattice3(X1,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_yellow_0(esk7_0,X1)
    | ~ r2_lattice3(esk7_0,X2,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_448]),c_0_26])).

cnf(c_0_454,negated_conjecture,
    ( r1_orders_2(esk6_0,k1_yellow_0(esk6_0,X1),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r1_yellow_0(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_451]),c_0_32])])).

cnf(c_0_455,negated_conjecture,
    ( ~ r1_orders_2(esk6_0,k1_yellow_0(esk6_0,esk8_0),esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_452,c_0_451])])).

cnf(c_0_456,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ r2_lattice3(esk7_0,X1,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_453,c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_457,negated_conjecture,
    ( r2_lattice3(esk7_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_328,c_0_447]),c_0_44]),c_0_25]),c_0_39])]),c_0_367])).

cnf(c_0_458,negated_conjecture,
    ( ~ r2_lattice3(esk6_0,esk8_0,esk3_3(esk7_0,esk8_0,k1_yellow_0(esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_454,c_0_37]),c_0_455])).

cnf(c_0_459,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_456,c_0_70]),c_0_457])]),c_0_458]),
    [proof]).

%------------------------------------------------------------------------------

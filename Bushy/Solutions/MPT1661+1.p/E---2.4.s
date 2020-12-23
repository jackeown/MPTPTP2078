%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t41_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:50 EDT 2019

% Result     : Theorem 277.99s
% Output     : CNFRefutation 277.99s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 672 expanded)
%              Number of clauses        :   45 ( 243 expanded)
%              Number of leaves         :    6 ( 172 expanded)
%              Depth                    :   13
%              Number of atoms          :  462 (6768 expanded)
%              Number of equality atoms :   11 (  54 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal clause size      :   67 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t41_waybel_0.p',d20_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t41_waybel_0.p',t4_subset)).

fof(t41_waybel_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                     => r2_hidden(k12_lattice3(X1,X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t41_waybel_0.p',t41_waybel_0)).

fof(t23_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k12_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t41_waybel_0.p',t23_yellow_0)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t41_waybel_0.p',dt_k12_lattice3)).

fof(d2_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X5,X3)
                                & r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t41_waybel_0.p',d2_waybel_0)).

fof(c_0_6,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ r2_hidden(X20,X19)
        | ~ r1_orders_2(X18,X20,X21)
        | r2_hidden(X21,X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk5_2(X18,X19),u1_struct_0(X18))
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk6_2(X18,X19),u1_struct_0(X18))
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(esk5_2(X18,X19),X19)
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk5_2(X18,X19),esk6_2(X18,X19))
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( ~ r2_hidden(esk6_2(X18,X19),X19)
        | v13_waybel_0(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_7,plain,(
    ! [X60,X61,X62] :
      ( ~ r2_hidden(X60,X61)
      | ~ m1_subset_1(X61,k1_zfmisc_1(X62))
      | m1_subset_1(X60,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_waybel_0(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( ( r2_hidden(X3,X2)
                          & r2_hidden(X4,X2) )
                       => r2_hidden(k12_lattice3(X1,X3,X4),X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_waybel_0])).

cnf(c_0_9,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,(
    ! [X10,X11] :
      ( v5_orders_2(esk1_0)
      & v2_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & v13_waybel_0(esk2_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( r2_hidden(esk3_0,esk2_0)
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( r2_hidden(esk4_0,esk2_0)
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( ~ r2_hidden(k12_lattice3(esk1_0,esk3_0,esk4_0),esk2_0)
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( v2_waybel_0(esk2_0,esk1_0)
        | ~ m1_subset_1(X10,u1_struct_0(esk1_0))
        | ~ m1_subset_1(X11,u1_struct_0(esk1_0))
        | ~ r2_hidden(X10,esk2_0)
        | ~ r2_hidden(X11,esk2_0)
        | r2_hidden(k12_lattice3(esk1_0,X10,X11),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_12,plain,(
    ! [X50,X51,X52,X53,X54] :
      ( ( r1_orders_2(X50,X53,X51)
        | X53 != k12_lattice3(X50,X51,X52)
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ v5_orders_2(X50)
        | ~ v2_lattice3(X50)
        | ~ l1_orders_2(X50) )
      & ( r1_orders_2(X50,X53,X52)
        | X53 != k12_lattice3(X50,X51,X52)
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ v5_orders_2(X50)
        | ~ v2_lattice3(X50)
        | ~ l1_orders_2(X50) )
      & ( ~ m1_subset_1(X54,u1_struct_0(X50))
        | ~ r1_orders_2(X50,X54,X51)
        | ~ r1_orders_2(X50,X54,X52)
        | r1_orders_2(X50,X54,X53)
        | X53 != k12_lattice3(X50,X51,X52)
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ v5_orders_2(X50)
        | ~ v2_lattice3(X50)
        | ~ l1_orders_2(X50) )
      & ( m1_subset_1(esk14_4(X50,X51,X52,X53),u1_struct_0(X50))
        | ~ r1_orders_2(X50,X53,X51)
        | ~ r1_orders_2(X50,X53,X52)
        | X53 = k12_lattice3(X50,X51,X52)
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ v5_orders_2(X50)
        | ~ v2_lattice3(X50)
        | ~ l1_orders_2(X50) )
      & ( r1_orders_2(X50,esk14_4(X50,X51,X52,X53),X51)
        | ~ r1_orders_2(X50,X53,X51)
        | ~ r1_orders_2(X50,X53,X52)
        | X53 = k12_lattice3(X50,X51,X52)
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ v5_orders_2(X50)
        | ~ v2_lattice3(X50)
        | ~ l1_orders_2(X50) )
      & ( r1_orders_2(X50,esk14_4(X50,X51,X52,X53),X52)
        | ~ r1_orders_2(X50,X53,X51)
        | ~ r1_orders_2(X50,X53,X52)
        | X53 = k12_lattice3(X50,X51,X52)
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ v5_orders_2(X50)
        | ~ v2_lattice3(X50)
        | ~ l1_orders_2(X50) )
      & ( ~ r1_orders_2(X50,esk14_4(X50,X51,X52,X53),X53)
        | ~ r1_orders_2(X50,X53,X51)
        | ~ r1_orders_2(X50,X53,X52)
        | X53 = k12_lattice3(X50,X51,X52)
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ v5_orders_2(X50)
        | ~ v2_lattice3(X50)
        | ~ l1_orders_2(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_yellow_0])])])])])).

fof(c_0_13,plain,(
    ! [X35,X36,X37] :
      ( ~ v5_orders_2(X35)
      | ~ v2_lattice3(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | ~ m1_subset_1(X37,u1_struct_0(X35))
      | m1_subset_1(k12_lattice3(X35,X36,X37),u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v13_waybel_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_orders_2(X2,X1,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X1,X4)
    | X5 != k12_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,k12_lattice3(X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_15])).

fof(c_0_25,plain,(
    ! [X24,X25,X26,X27,X31] :
      ( ( m1_subset_1(esk7_4(X24,X25,X26,X27),u1_struct_0(X24))
        | ~ r2_hidden(X26,X25)
        | ~ r2_hidden(X27,X25)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( r2_hidden(esk7_4(X24,X25,X26,X27),X25)
        | ~ r2_hidden(X26,X25)
        | ~ r2_hidden(X27,X25)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( r1_orders_2(X24,esk7_4(X24,X25,X26,X27),X26)
        | ~ r2_hidden(X26,X25)
        | ~ r2_hidden(X27,X25)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( r1_orders_2(X24,esk7_4(X24,X25,X26,X27),X27)
        | ~ r2_hidden(X26,X25)
        | ~ r2_hidden(X27,X25)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk8_2(X24,X25),u1_struct_0(X24))
        | v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk9_2(X24,X25),u1_struct_0(X24))
        | v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( r2_hidden(esk8_2(X24,X25),X25)
        | v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( r2_hidden(esk9_2(X24,X25),X25)
        | v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X24))
        | ~ r2_hidden(X31,X25)
        | ~ r1_orders_2(X24,X31,esk8_2(X24,X25))
        | ~ r1_orders_2(X24,X31,esk9_2(X24,X25))
        | v2_waybel_0(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_waybel_0])])])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,X3,X2)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r2_hidden(X3,esk2_0)
    | ~ m1_subset_1(k12_lattice3(esk1_0,X1,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,esk7_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,X3,X2)
    | ~ r1_orders_2(esk1_0,X3,X1)
    | ~ r2_hidden(X3,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_17]),c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,esk7_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_27,c_0_10]),c_0_10])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,esk7_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v2_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,X1,esk8_2(X2,X3))
    | ~ r1_orders_2(X2,X1,esk9_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ r1_orders_2(esk1_0,esk7_4(esk1_0,X3,X4,X2),X1)
    | ~ r2_hidden(esk7_4(esk1_0,X3,X4,X2),esk2_0)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | ~ v2_waybel_0(X3,esk1_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_17])]),c_0_10])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,esk7_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_30,c_0_10]),c_0_10])).

cnf(c_0_35,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( v2_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,X3,esk8_2(X2,X1))
    | ~ r1_orders_2(X2,X3,esk9_2(X2,X1))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_31,c_0_10])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_19])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk9_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(esk7_4(esk1_0,X3,X1,X2),esk2_0)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ v2_waybel_0(X3,esk1_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_17])]),c_0_10])).

cnf(c_0_42,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_35,c_0_10]),c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_36,c_0_24]),c_0_24])).

cnf(c_0_44,plain,
    ( v2_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,k12_lattice3(X2,X3,esk9_2(X2,X1)),esk8_2(X2,X1))
    | ~ r2_hidden(k12_lattice3(X2,X3,esk9_2(X2,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_19])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk8_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_15]),c_0_17])]),c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,plain,
    ( v2_waybel_0(X1,X2)
    | ~ r2_hidden(k12_lattice3(X2,esk8_2(X2,X1),esk9_2(X2,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_39]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk9_2(esk1_0,esk2_0),esk2_0)
    | ~ r2_hidden(esk8_2(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_15]),c_0_17]),c_0_22]),c_0_23])]),c_0_52])).

cnf(c_0_54,plain,
    ( r2_hidden(esk9_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk8_2(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_15]),c_0_17])]),c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_15]),c_0_17])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------

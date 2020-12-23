%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1661+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 891 expanded)
%              Number of clauses        :   52 ( 311 expanded)
%              Number of leaves         :    5 ( 218 expanded)
%              Depth                    :   13
%              Number of atoms          :  484 (11159 expanded)
%              Number of equality atoms :   11 ( 117 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   67 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(c_0_5,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( r1_orders_2(X23,X26,X24)
        | X26 != k12_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,X26,X25)
        | X26 != k12_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ r1_orders_2(X23,X27,X24)
        | ~ r1_orders_2(X23,X27,X25)
        | r1_orders_2(X23,X27,X26)
        | X26 != k12_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk6_4(X23,X24,X25,X26),u1_struct_0(X23))
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k12_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,esk6_4(X23,X24,X25,X26),X24)
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k12_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,esk6_4(X23,X24,X25,X26),X25)
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k12_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,esk6_4(X23,X24,X25,X26),X26)
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k12_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_yellow_0])])])])])).

fof(c_0_6,plain,(
    ! [X20,X21,X22] :
      ( ~ v5_orders_2(X20)
      | ~ v2_lattice3(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | m1_subset_1(k12_lattice3(X20,X21,X22),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

fof(c_0_7,negated_conjecture,(
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

cnf(c_0_8,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,(
    ! [X33,X34] :
      ( v5_orders_2(esk7_0)
      & v2_lattice3(esk7_0)
      & l1_orders_2(esk7_0)
      & v13_waybel_0(esk8_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
      & ( m1_subset_1(esk9_0,u1_struct_0(esk7_0))
        | ~ v2_waybel_0(esk8_0,esk7_0) )
      & ( m1_subset_1(esk10_0,u1_struct_0(esk7_0))
        | ~ v2_waybel_0(esk8_0,esk7_0) )
      & ( r2_hidden(esk9_0,esk8_0)
        | ~ v2_waybel_0(esk8_0,esk7_0) )
      & ( r2_hidden(esk10_0,esk8_0)
        | ~ v2_waybel_0(esk8_0,esk7_0) )
      & ( ~ r2_hidden(k12_lattice3(esk7_0,esk9_0,esk10_0),esk8_0)
        | ~ v2_waybel_0(esk8_0,esk7_0) )
      & ( v2_waybel_0(esk8_0,esk7_0)
        | ~ m1_subset_1(X33,u1_struct_0(esk7_0))
        | ~ m1_subset_1(X34,u1_struct_0(esk7_0))
        | ~ r2_hidden(X33,esk8_0)
        | ~ r2_hidden(X34,esk8_0)
        | r2_hidden(k12_lattice3(esk7_0,X33,X34),esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

fof(c_0_11,plain,(
    ! [X12,X13,X14,X15,X19] :
      ( ( m1_subset_1(esk3_4(X12,X13,X14,X15),u1_struct_0(X12))
        | ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk3_4(X12,X13,X14,X15),X13)
        | ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( r1_orders_2(X12,esk3_4(X12,X13,X14,X15),X14)
        | ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( r1_orders_2(X12,esk3_4(X12,X13,X14,X15),X15)
        | ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk4_2(X12,X13),u1_struct_0(X12))
        | v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk5_2(X12,X13),u1_struct_0(X12))
        | v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk4_2(X12,X13),X13)
        | v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk5_2(X12,X13),X13)
        | v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X12))
        | ~ r2_hidden(X19,X13)
        | ~ r1_orders_2(X12,X19,esk4_2(X12,X13))
        | ~ r1_orders_2(X12,X19,esk5_2(X12,X13))
        | v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_waybel_0])])])])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X3)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k12_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( v2_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,X1,esk4_2(X2,X3))
    | ~ r1_orders_2(X2,X1,esk5_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_orders_2(esk7_0,k12_lattice3(esk7_0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk7_0,X1,X2),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,k12_lattice3(X1,X2,X3),X2)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_9])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( v2_waybel_0(X1,esk7_0)
    | ~ r1_orders_2(esk7_0,k12_lattice3(esk7_0,X2,esk5_2(esk7_0,X1)),esk4_2(esk7_0,X1))
    | ~ r2_hidden(k12_lattice3(esk7_0,X2,esk5_2(esk7_0,X1)),X1)
    | ~ m1_subset_1(esk5_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15])]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk7_0,k12_lattice3(esk7_0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( v2_waybel_0(esk8_0,esk7_0)
    | r2_hidden(k12_lattice3(esk7_0,X1,X2),esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_26,plain,(
    ! [X6,X7,X8,X9] :
      ( ( ~ v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(X8,X7)
        | ~ r1_orders_2(X6,X8,X9)
        | r2_hidden(X9,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_2(X6,X7),u1_struct_0(X6))
        | v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk1_2(X6,X7),esk2_2(X6,X7))
        | v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X7),X7)
        | v13_waybel_0(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,X2,k12_lattice3(X1,X3,X4))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( v2_waybel_0(X1,esk7_0)
    | ~ r2_hidden(k12_lattice3(esk7_0,esk4_2(esk7_0,X1),esk5_2(esk7_0,X1)),X1)
    | ~ m1_subset_1(esk5_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk4_2(esk7_0,X1),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v2_waybel_0(esk8_0,esk7_0)
    | v2_waybel_0(X1,esk7_0)
    | r2_hidden(k12_lattice3(esk7_0,X2,esk5_2(esk7_0,X1)),esk8_0)
    | ~ r2_hidden(esk5_2(esk7_0,X1),esk8_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk7_0,X1,k12_lattice3(esk7_0,X2,X3))
    | ~ r1_orders_2(esk7_0,X1,X3)
    | ~ r1_orders_2(esk7_0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_33,negated_conjecture,
    ( v2_waybel_0(esk8_0,esk7_0)
    | ~ r2_hidden(esk5_2(esk7_0,esk8_0),esk8_0)
    | ~ r2_hidden(esk4_2(esk7_0,esk8_0),esk8_0)
    | ~ m1_subset_1(esk5_2(esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk4_2(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk7_0,X1,X2),X3)
    | ~ r1_orders_2(esk7_0,X4,X2)
    | ~ r1_orders_2(esk7_0,X4,X1)
    | ~ r2_hidden(X4,X3)
    | ~ v13_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X4,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15])]),c_0_19])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( v2_waybel_0(esk8_0,esk7_0)
    | ~ r2_hidden(esk4_2(esk7_0,esk8_0),esk8_0)
    | ~ m1_subset_1(esk5_2(esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk4_2(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk7_0,X1,X2),X3)
    | ~ v2_waybel_0(X4,esk7_0)
    | ~ r1_orders_2(esk7_0,esk3_4(esk7_0,X4,X5,X2),X1)
    | ~ r2_hidden(esk3_4(esk7_0,X4,X5,X2),X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X5,X4)
    | ~ v13_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(esk3_4(esk7_0,X4,X5,X2),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X5,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15])])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( v2_waybel_0(esk8_0,esk7_0)
    | ~ r2_hidden(esk4_2(esk7_0,esk8_0),esk8_0)
    | ~ m1_subset_1(esk4_2(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_30]),c_0_15])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk7_0,X1,X2),X3)
    | ~ v2_waybel_0(X4,esk7_0)
    | ~ r2_hidden(esk3_4(esk7_0,X4,X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ v13_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(esk3_4(esk7_0,X4,X1,X2),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_15])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( v2_waybel_0(esk8_0,esk7_0)
    | ~ m1_subset_1(esk4_2(esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_30]),c_0_15])])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk7_0,X1,X2),X3)
    | ~ v2_waybel_0(X3,esk7_0)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ v13_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(esk3_4(esk7_0,X3,X1,X2),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_15])])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(esk7_0,esk9_0,esk10_0),esk8_0)
    | ~ v2_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( v2_waybel_0(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_30]),c_0_15])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk7_0,X1,X2),X3)
    | ~ v2_waybel_0(X3,esk7_0)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ v13_waybel_0(X3,esk7_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_15])])).

cnf(c_0_51,negated_conjecture,
    ( v13_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0)
    | ~ v2_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ v2_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk7_0))
    | ~ v2_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0))
    | ~ v2_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(esk7_0,esk9_0,esk10_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k12_lattice3(esk7_0,X1,X2),esk8_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_49]),c_0_30])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_49])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_49])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_49])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_49])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61])]),
    [proof]).

%------------------------------------------------------------------------------

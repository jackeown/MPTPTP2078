%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:28 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :  174 (416694 expanded)
%              Number of clauses        :  149 (142935 expanded)
%              Number of leaves         :   12 (134248 expanded)
%              Depth                    :   62
%              Number of atoms          :  725 (4103396 expanded)
%              Number of equality atoms :  146 (385276 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r2_yellow_0(X1,X5)
                                  & X4 = k2_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                    <=> r1_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t4_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => ! [X4] :
                    ( ( r1_lattice3(X1,X4,X3)
                     => r1_lattice3(X1,X4,X2) )
                    & ( r2_lattice3(X1,X4,X2)
                     => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(t7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X2,X3) )
                & ( r1_orders_2(X1,X2,X3)
                 => r1_lattice3(X1,k1_tarski(X3),X2) )
                & ( r2_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X3,X2) )
                & ( r1_orders_2(X1,X3,X2)
                 => r2_lattice3(X1,k1_tarski(X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_11,plain,(
    ! [X2,X1,X3] :
      ( epred1_3(X3,X1,X2)
    <=> ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) ) ) ),
    introduced(definition)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( epred1_3(X3,X1,X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X2,X4)
                      <=> r1_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t57_waybel_0]),c_0_11])).

fof(c_0_13,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk1_3(X22,X23,X24),u1_struct_0(X22))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk1_3(X22,X23,X24),X23)
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X24,esk1_3(X22,X23,X24))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & epred1_3(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & ( ~ r1_lattice3(esk3_0,esk4_0,esk6_0)
      | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r1_lattice3(esk3_0,esk4_0,esk6_0)
      | r1_lattice3(esk3_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | m1_subset_1(k1_tarski(X10),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_21,plain,(
    ! [X2,X1,X3] :
      ( epred1_3(X3,X1,X2)
     => ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X43,X44,X45,X46,X47,X49] :
      ( ( ~ v1_finset_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X43))
        | X46 = k1_xboole_0
        | r2_yellow_0(X44,X46)
        | ~ epred1_3(X45,X44,X43) )
      & ( v1_finset_1(esk7_4(X43,X44,X45,X47))
        | ~ r2_hidden(X47,X45)
        | ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ epred1_3(X45,X44,X43) )
      & ( m1_subset_1(esk7_4(X43,X44,X45,X47),k1_zfmisc_1(X43))
        | ~ r2_hidden(X47,X45)
        | ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ epred1_3(X45,X44,X43) )
      & ( r2_yellow_0(X44,esk7_4(X43,X44,X45,X47))
        | ~ r2_hidden(X47,X45)
        | ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ epred1_3(X45,X44,X43) )
      & ( X47 = k2_yellow_0(X44,esk7_4(X43,X44,X45,X47))
        | ~ r2_hidden(X47,X45)
        | ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ epred1_3(X45,X44,X43) )
      & ( ~ v1_finset_1(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X43))
        | X49 = k1_xboole_0
        | r2_hidden(k2_yellow_0(X44,X49),X45)
        | ~ epred1_3(X45,X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18])])).

fof(c_0_28,plain,(
    ! [X15] : v1_finset_1(k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

fof(c_0_29,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( epred1_3(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_41,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ r1_lattice3(X32,X35,X34)
        | r1_lattice3(X32,X35,X33)
        | ~ r1_orders_2(X32,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v4_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ r2_lattice3(X32,X35,X33)
        | r2_lattice3(X32,X35,X34)
        | ~ r1_orders_2(X32,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v4_orders_2(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

cnf(c_0_42,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18])])).

fof(c_0_43,plain,(
    ! [X27,X28,X29,X30] :
      ( ( r1_lattice3(X27,X28,X29)
        | X29 != k2_yellow_0(X27,X28)
        | ~ r2_yellow_0(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r1_lattice3(X27,X28,X30)
        | r1_orders_2(X27,X30,X29)
        | X29 != k2_yellow_0(X27,X28)
        | ~ r2_yellow_0(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk2_3(X27,X28,X29),u1_struct_0(X27))
        | ~ r1_lattice3(X27,X28,X29)
        | X29 = k2_yellow_0(X27,X28)
        | ~ r2_yellow_0(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( r1_lattice3(X27,X28,esk2_3(X27,X28,X29))
        | ~ r1_lattice3(X27,X28,X29)
        | X29 = k2_yellow_0(X27,X28)
        | ~ r2_yellow_0(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,esk2_3(X27,X28,X29),X29)
        | ~ r1_lattice3(X27,X28,X29)
        | X29 = k2_yellow_0(X27,X28)
        | ~ r2_yellow_0(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_45,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r1_lattice3(X36,k1_tarski(X38),X37)
        | r1_orders_2(X36,X37,X38)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( ~ r1_orders_2(X36,X37,X38)
        | r1_lattice3(X36,k1_tarski(X38),X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( ~ r2_lattice3(X36,k1_tarski(X38),X37)
        | r1_orders_2(X36,X38,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ l1_orders_2(X36) )
      & ( ~ r1_orders_2(X36,X38,X37)
        | r2_lattice3(X36,k1_tarski(X38),X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

cnf(c_0_46,plain,
    ( r1_lattice3(X1,X2,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_17])])).

cnf(c_0_49,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ epred1_3(X2,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_32])])).

cnf(c_0_51,plain,
    ( r1_orders_2(X1,X3,X2)
    | ~ r1_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,esk6_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_17]),c_0_47]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_55,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,X1)
    | ~ r1_lattice3(esk3_0,k1_tarski(X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_17]),c_0_18])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_40]),c_0_18])]),c_0_56])).

cnf(c_0_61,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_17]),c_0_18])])).

cnf(c_0_65,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,plain,
    ( X1 = k2_yellow_0(X2,esk7_4(X3,X2,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_68,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_66]),c_0_27])).

cnf(c_0_69,plain,
    ( k2_yellow_0(esk3_0,esk7_4(X1,esk3_0,X2,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ epred1_3(X2,esk3_0,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_71])).

cnf(c_0_73,plain,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_72]),c_0_32])])).

cnf(c_0_74,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_75]),c_0_18])])).

cnf(c_0_77,plain,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_72]),c_0_32])])).

cnf(c_0_78,plain,
    ( r2_yellow_0(X1,esk7_4(X2,X1,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_79,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_71]),c_0_17])]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_36])).

cnf(c_0_81,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_82,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(X1,esk3_0,X2,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ epred1_3(X2,esk3_0,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_79]),c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_75]),c_0_18])]),c_0_80])).

cnf(c_0_86,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X1)
    | ~ r1_lattice3(esk3_0,X1,esk6_0)
    | ~ m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_17]),c_0_18])])).

cnf(c_0_91,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_20])).

cnf(c_0_92,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_94,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | ~ r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_92])).

cnf(c_0_96,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(X1,esk3_0,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))
    | ~ epred1_3(X2,esk3_0,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_68])).

cnf(c_0_97,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_27])).

cnf(c_0_98,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_95]),c_0_71])).

cnf(c_0_99,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_36])).

cnf(c_0_100,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_27]),c_0_64])).

fof(c_0_101,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_102,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_20])).

cnf(c_0_103,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_100])).

cnf(c_0_104,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_103]),c_0_18])])).

cnf(c_0_107,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_108,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(X1,esk4_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X1,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_17])]),c_0_26])).

cnf(c_0_110,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_20])).

cnf(c_0_111,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_100])).

cnf(c_0_112,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_102])).

cnf(c_0_113,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_64])).

cnf(c_0_114,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_111]),c_0_18])])).

cnf(c_0_115,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(X1,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_113]),c_0_26])).

cnf(c_0_117,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_107]),c_0_17])]),c_0_52])).

cnf(c_0_118,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_20])).

cnf(c_0_119,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_98]),c_0_68])).

cnf(c_0_120,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_64])).

cnf(c_0_121,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_119]),c_0_26])).

cnf(c_0_122,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_120]),c_0_52])).

cnf(c_0_123,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ epred1_3(X2,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_121]),c_0_32])])).

cnf(c_0_124,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_98]),c_0_58])).

cnf(c_0_125,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_36])).

cnf(c_0_126,plain,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))
    | ~ epred1_3(X2,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_121]),c_0_32])])).

cnf(c_0_127,plain,
    ( r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_128,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_124]),c_0_52])).

cnf(c_0_129,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_36])).

cnf(c_0_131,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_132,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ r1_orders_2(esk3_0,X2,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_47]),c_0_18])])).

cnf(c_0_133,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X1)
    | ~ r1_lattice3(esk3_0,k1_tarski(X1),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_129]),c_0_18])])).

cnf(c_0_134,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_129]),c_0_18])]),c_0_130])).

cnf(c_0_135,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(X1),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | ~ r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_129]),c_0_18])])).

cnf(c_0_136,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_129]),c_0_18])])).

cnf(c_0_137,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_138,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r2_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | ~ r1_orders_2(esk3_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_129])).

cnf(c_0_139,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_128]),c_0_134])).

cnf(c_0_140,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk6_0),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | ~ r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_17])).

cnf(c_0_141,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_100]),c_0_17])]),c_0_125])).

cnf(c_0_142,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_102]),c_0_17])]),c_0_125])).

cnf(c_0_143,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_128]),c_0_18])])).

cnf(c_0_144,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r2_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_145,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk6_0),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_146,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_142]),c_0_129])).

cnf(c_0_147,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r2_lattice3(esk3_0,k1_tarski(esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_17])).

cnf(c_0_148,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k1_tarski(esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_149,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | ~ r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_128])).

cnf(c_0_150,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_134])).

cnf(c_0_151,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_153,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_151])).

cnf(c_0_154,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0)
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_152])).

cnf(c_0_155,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_153]),c_0_100])).

cnf(c_0_156,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_154]),c_0_102])).

cnf(c_0_157,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))
    | ~ r1_lattice3(esk3_0,X2,X1)
    | ~ r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_155]),c_0_18])])).

cnf(c_0_158,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_156])).

cnf(c_0_159,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_107]),c_0_17])])).

cnf(c_0_160,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_20])).

cnf(c_0_161,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_64])).

cnf(c_0_162,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))
    | ~ m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_161])).

cnf(c_0_163,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_98]),c_0_27]),c_0_64])).

cnf(c_0_164,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_163]),c_0_17])]),c_0_125])).

cnf(c_0_165,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_164]),c_0_129])).

cnf(c_0_166,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_165,c_0_134])).

cnf(c_0_167,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_166])).

fof(c_0_168,plain,(
    ! [X6] : ~ v1_xboole_0(k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_169,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_167])).

cnf(c_0_170,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_168])).

cnf(c_0_171,negated_conjecture,
    ( k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_169]),c_0_163])).

cnf(c_0_172,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_173,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_172])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.32/4.54  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 4.32/4.54  # and selection function SelectNewComplexAHP.
% 4.32/4.54  #
% 4.32/4.54  # Preprocessing time       : 0.030 s
% 4.32/4.54  # Presaturation interreduction done
% 4.32/4.54  
% 4.32/4.54  # Proof found!
% 4.32/4.54  # SZS status Theorem
% 4.32/4.54  # SZS output start CNFRefutation
% 4.32/4.54  fof(t57_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_waybel_0)).
% 4.32/4.54  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 4.32/4.54  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.32/4.54  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 4.32/4.54  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.32/4.54  fof(t4_yellow_0, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_0)).
% 4.32/4.54  fof(d10_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_yellow_0(X1,X2)=>(X3=k2_yellow_0(X1,X2)<=>(r1_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 4.32/4.54  fof(t7_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((((r1_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X2,X3))&(r1_orders_2(X1,X2,X3)=>r1_lattice3(X1,k1_tarski(X3),X2)))&(r2_lattice3(X1,k1_tarski(X3),X2)=>r1_orders_2(X1,X3,X2)))&(r1_orders_2(X1,X3,X2)=>r2_lattice3(X1,k1_tarski(X3),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 4.32/4.54  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.32/4.54  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.32/4.54  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.32/4.54  fof(c_0_11, plain, ![X2, X1, X3]:(epred1_3(X3,X1,X2)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), introduced(definition)).
% 4.32/4.54  fof(c_0_12, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred1_3(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t57_waybel_0]), c_0_11])).
% 4.32/4.54  fof(c_0_13, plain, ![X22, X23, X24, X25]:((~r1_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X23)|r1_orders_2(X22,X24,X25)))|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((m1_subset_1(esk1_3(X22,X23,X24),u1_struct_0(X22))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_hidden(esk1_3(X22,X23,X24),X23)|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,X24,esk1_3(X22,X23,X24))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 4.32/4.54  fof(c_0_14, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred1_3(esk5_0,esk3_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r1_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0))&(r1_lattice3(esk3_0,esk4_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 4.32/4.54  fof(c_0_15, plain, ![X10, X11]:(~r2_hidden(X10,X11)|m1_subset_1(k1_tarski(X10),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 4.32/4.54  cnf(c_0_16, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.32/4.54  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.54  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.54  cnf(c_0_19, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.32/4.54  cnf(c_0_20, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 4.32/4.54  fof(c_0_21, plain, ![X2, X1, X3]:(epred1_3(X3,X1,X2)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r2_yellow_0(X1,X5)&X4=k2_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k2_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_11])).
% 4.32/4.54  cnf(c_0_22, negated_conjecture, (~r1_lattice3(esk3_0,esk4_0,esk6_0)|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.54  cnf(c_0_23, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 4.32/4.54  cnf(c_0_24, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.32/4.54  fof(c_0_25, plain, ![X43, X44, X45, X46, X47, X49]:(((~v1_finset_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43))|(X46=k1_xboole_0|r2_yellow_0(X44,X46))|~epred1_3(X45,X44,X43))&(((v1_finset_1(esk7_4(X43,X44,X45,X47))|~r2_hidden(X47,X45)|~m1_subset_1(X47,u1_struct_0(X44))|~epred1_3(X45,X44,X43))&(m1_subset_1(esk7_4(X43,X44,X45,X47),k1_zfmisc_1(X43))|~r2_hidden(X47,X45)|~m1_subset_1(X47,u1_struct_0(X44))|~epred1_3(X45,X44,X43)))&((r2_yellow_0(X44,esk7_4(X43,X44,X45,X47))|~r2_hidden(X47,X45)|~m1_subset_1(X47,u1_struct_0(X44))|~epred1_3(X45,X44,X43))&(X47=k2_yellow_0(X44,esk7_4(X43,X44,X45,X47))|~r2_hidden(X47,X45)|~m1_subset_1(X47,u1_struct_0(X44))|~epred1_3(X45,X44,X43)))))&(~v1_finset_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(X43))|(X49=k1_xboole_0|r2_hidden(k2_yellow_0(X44,X49),X45))|~epred1_3(X45,X44,X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])])).
% 4.32/4.54  cnf(c_0_26, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 4.32/4.54  cnf(c_0_27, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_18])])).
% 4.32/4.54  fof(c_0_28, plain, ![X15]:v1_finset_1(k1_tarski(X15)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 4.32/4.54  fof(c_0_29, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 4.32/4.54  cnf(c_0_30, plain, (X1=k1_xboole_0|r2_hidden(k2_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.32/4.54  cnf(c_0_31, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 4.32/4.54  cnf(c_0_32, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.32/4.54  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.32/4.54  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.54  cnf(c_0_35, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 4.32/4.54  cnf(c_0_36, negated_conjecture, (epred1_3(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.54  cnf(c_0_37, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 4.32/4.54  cnf(c_0_38, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 4.32/4.54  cnf(c_0_39, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.32/4.54  cnf(c_0_40, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 4.32/4.54  fof(c_0_41, plain, ![X32, X33, X34, X35]:((~r1_lattice3(X32,X35,X34)|r1_lattice3(X32,X35,X33)|~r1_orders_2(X32,X33,X34)|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(~v4_orders_2(X32)|~l1_orders_2(X32)))&(~r2_lattice3(X32,X35,X33)|r2_lattice3(X32,X35,X34)|~r1_orders_2(X32,X33,X34)|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(~v4_orders_2(X32)|~l1_orders_2(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).
% 4.32/4.54  cnf(c_0_42, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18])])).
% 4.32/4.54  fof(c_0_43, plain, ![X27, X28, X29, X30]:(((r1_lattice3(X27,X28,X29)|X29!=k2_yellow_0(X27,X28)|~r2_yellow_0(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))&(~m1_subset_1(X30,u1_struct_0(X27))|(~r1_lattice3(X27,X28,X30)|r1_orders_2(X27,X30,X29))|X29!=k2_yellow_0(X27,X28)|~r2_yellow_0(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27)))&((m1_subset_1(esk2_3(X27,X28,X29),u1_struct_0(X27))|~r1_lattice3(X27,X28,X29)|X29=k2_yellow_0(X27,X28)|~r2_yellow_0(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))&((r1_lattice3(X27,X28,esk2_3(X27,X28,X29))|~r1_lattice3(X27,X28,X29)|X29=k2_yellow_0(X27,X28)|~r2_yellow_0(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))&(~r1_orders_2(X27,esk2_3(X27,X28,X29),X29)|~r1_lattice3(X27,X28,X29)|X29=k2_yellow_0(X27,X28)|~r2_yellow_0(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).
% 4.32/4.54  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.32/4.54  fof(c_0_45, plain, ![X36, X37, X38]:((((~r1_lattice3(X36,k1_tarski(X38),X37)|r1_orders_2(X36,X37,X38)|~m1_subset_1(X38,u1_struct_0(X36))|~m1_subset_1(X37,u1_struct_0(X36))|~l1_orders_2(X36))&(~r1_orders_2(X36,X37,X38)|r1_lattice3(X36,k1_tarski(X38),X37)|~m1_subset_1(X38,u1_struct_0(X36))|~m1_subset_1(X37,u1_struct_0(X36))|~l1_orders_2(X36)))&(~r2_lattice3(X36,k1_tarski(X38),X37)|r1_orders_2(X36,X38,X37)|~m1_subset_1(X38,u1_struct_0(X36))|~m1_subset_1(X37,u1_struct_0(X36))|~l1_orders_2(X36)))&(~r1_orders_2(X36,X38,X37)|r2_lattice3(X36,k1_tarski(X38),X37)|~m1_subset_1(X38,u1_struct_0(X36))|~m1_subset_1(X37,u1_struct_0(X36))|~l1_orders_2(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).
% 4.32/4.54  cnf(c_0_46, plain, (r1_lattice3(X1,X2,X4)|~r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.32/4.54  cnf(c_0_47, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.54  cnf(c_0_48, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_27]), c_0_17])])).
% 4.32/4.54  cnf(c_0_49, plain, (r1_lattice3(X1,X2,X3)|X3!=k2_yellow_0(X1,X2)|~r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.32/4.54  cnf(c_0_50, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~epred1_3(X2,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_32])])).
% 4.32/4.54  cnf(c_0_51, plain, (r1_orders_2(X1,X3,X2)|~r1_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 4.32/4.54  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_27])).
% 4.32/4.54  cnf(c_0_53, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,esk6_0,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_17]), c_0_47]), c_0_18])])).
% 4.32/4.54  cnf(c_0_54, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_38])).
% 4.32/4.54  cnf(c_0_55, plain, (r1_lattice3(X1,X2,k2_yellow_0(X1,X2))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)|~m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))), inference(er,[status(thm)],[c_0_49])).
% 4.32/4.54  cnf(c_0_56, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 4.32/4.54  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,X1)|~r1_lattice3(esk3_0,k1_tarski(X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_17]), c_0_18])])).
% 4.32/4.54  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_27])).
% 4.32/4.54  cnf(c_0_59, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_40])).
% 4.32/4.54  cnf(c_0_60, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_40]), c_0_18])]), c_0_56])).
% 4.32/4.54  cnf(c_0_61, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.32/4.54  cnf(c_0_62, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 4.32/4.54  cnf(c_0_63, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 4.32/4.54  cnf(c_0_64, negated_conjecture, (r1_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,X1,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_17]), c_0_18])])).
% 4.32/4.54  cnf(c_0_65, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 4.32/4.54  cnf(c_0_66, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 4.32/4.54  cnf(c_0_67, plain, (X1=k2_yellow_0(X2,esk7_4(X3,X2,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.32/4.54  cnf(c_0_68, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_66]), c_0_27])).
% 4.32/4.54  cnf(c_0_69, plain, (k2_yellow_0(esk3_0,esk7_4(X1,esk3_0,X2,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~epred1_3(X2,esk3_0,X1)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 4.32/4.54  cnf(c_0_70, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_36])).
% 4.32/4.54  cnf(c_0_71, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_20])).
% 4.32/4.54  cnf(c_0_72, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_71])).
% 4.32/4.54  cnf(c_0_73, plain, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_72]), c_0_32])])).
% 4.32/4.54  cnf(c_0_74, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_36])).
% 4.32/4.54  cnf(c_0_75, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_74])).
% 4.32/4.54  cnf(c_0_76, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_75]), c_0_18])])).
% 4.32/4.54  cnf(c_0_77, plain, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_72]), c_0_32])])).
% 4.32/4.54  cnf(c_0_78, plain, (r2_yellow_0(X1,esk7_4(X2,X1,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred1_3(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.32/4.54  cnf(c_0_79, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_71]), c_0_17])]), c_0_74])).
% 4.32/4.54  cnf(c_0_80, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_77, c_0_36])).
% 4.32/4.54  cnf(c_0_81, plain, (r1_orders_2(X2,X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|X4!=k2_yellow_0(X2,X3)|~r2_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.32/4.54  cnf(c_0_82, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(X1,esk3_0,X2,esk1_3(esk3_0,esk5_0,esk6_0)))|~epred1_3(X2,esk3_0,X1)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_78, c_0_68])).
% 4.32/4.54  cnf(c_0_83, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_71])).
% 4.32/4.54  cnf(c_0_84, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_79]), c_0_75])).
% 4.32/4.54  cnf(c_0_85, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_75]), c_0_18])]), c_0_80])).
% 4.32/4.54  cnf(c_0_86, plain, (r1_orders_2(X1,X2,k2_yellow_0(X1,X3))|~r2_yellow_0(X1,X3)|~r1_lattice3(X1,X3,X2)|~l1_orders_2(X1)|~m1_subset_1(k2_yellow_0(X1,X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_81])).
% 4.32/4.54  cnf(c_0_87, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_36])).
% 4.32/4.54  cnf(c_0_88, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_83])).
% 4.32/4.54  cnf(c_0_89, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 4.32/4.54  cnf(c_0_90, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,X1))|~r2_yellow_0(esk3_0,X1)|~r1_lattice3(esk3_0,X1,esk6_0)|~m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_17]), c_0_18])])).
% 4.32/4.54  cnf(c_0_91, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_20])).
% 4.32/4.54  cnf(c_0_92, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 4.32/4.54  cnf(c_0_93, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~epred1_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.32/4.54  cnf(c_0_94, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|~r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|~m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 4.32/4.54  cnf(c_0_95, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_92])).
% 4.32/4.54  cnf(c_0_96, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(X1,esk3_0,X2,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(X1))|~epred1_3(X2,esk3_0,X1)|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),X2)), inference(spm,[status(thm)],[c_0_93, c_0_68])).
% 4.32/4.54  cnf(c_0_97, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_27])).
% 4.32/4.54  cnf(c_0_98, negated_conjecture, (k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_95]), c_0_71])).
% 4.32/4.54  cnf(c_0_99, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_96, c_0_36])).
% 4.32/4.54  cnf(c_0_100, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_27]), c_0_64])).
% 4.32/4.54  fof(c_0_101, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 4.32/4.54  cnf(c_0_102, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_20])).
% 4.32/4.54  cnf(c_0_103, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_100])).
% 4.32/4.54  cnf(c_0_104, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 4.32/4.54  cnf(c_0_105, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_102])).
% 4.32/4.54  cnf(c_0_106, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_103]), c_0_18])])).
% 4.32/4.54  cnf(c_0_107, negated_conjecture, (r1_lattice3(esk3_0,esk4_0,esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.32/4.54  cnf(c_0_108, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(X1,esk4_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(X1,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 4.32/4.54  cnf(c_0_109, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_17])]), c_0_26])).
% 4.32/4.54  cnf(c_0_110, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_108, c_0_20])).
% 4.32/4.54  cnf(c_0_111, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_100])).
% 4.32/4.54  cnf(c_0_112, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_102])).
% 4.32/4.54  cnf(c_0_113, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_64])).
% 4.32/4.54  cnf(c_0_114, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_111]), c_0_18])])).
% 4.32/4.54  cnf(c_0_115, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(X1,esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(X1,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_104, c_0_112])).
% 4.32/4.54  cnf(c_0_116, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))|~m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_113]), c_0_26])).
% 4.32/4.54  cnf(c_0_117, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_107]), c_0_17])]), c_0_52])).
% 4.32/4.54  cnf(c_0_118, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_115, c_0_20])).
% 4.32/4.54  cnf(c_0_119, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_98]), c_0_68])).
% 4.32/4.54  cnf(c_0_120, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_64])).
% 4.32/4.54  cnf(c_0_121, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_119]), c_0_26])).
% 4.32/4.54  cnf(c_0_122, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))|~m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_120]), c_0_52])).
% 4.32/4.54  cnf(c_0_123, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~epred1_3(X2,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_121]), c_0_32])])).
% 4.32/4.54  cnf(c_0_124, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_98]), c_0_58])).
% 4.32/4.54  cnf(c_0_125, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_123, c_0_36])).
% 4.32/4.54  cnf(c_0_126, plain, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(X1,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))|~epred1_3(X2,X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_121]), c_0_32])])).
% 4.32/4.54  cnf(c_0_127, plain, (r2_lattice3(X1,X2,X4)|~r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.32/4.54  cnf(c_0_128, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk4_0,esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_124]), c_0_52])).
% 4.32/4.54  cnf(c_0_129, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_125])).
% 4.32/4.54  cnf(c_0_130, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_126, c_0_36])).
% 4.32/4.54  cnf(c_0_131, plain, (r2_lattice3(X1,k1_tarski(X2),X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 4.32/4.54  cnf(c_0_132, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r2_lattice3(esk3_0,X1,X2)|~r1_orders_2(esk3_0,X2,esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_47]), c_0_18])])).
% 4.32/4.54  cnf(c_0_133, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X1)|~r1_lattice3(esk3_0,k1_tarski(X1),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_129]), c_0_18])])).
% 4.32/4.54  cnf(c_0_134, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_129]), c_0_18])]), c_0_130])).
% 4.32/4.54  cnf(c_0_135, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(X1),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|~r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_129]), c_0_18])])).
% 4.32/4.54  cnf(c_0_136, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_129]), c_0_18])])).
% 4.32/4.54  cnf(c_0_137, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k1_tarski(X2),X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 4.32/4.54  cnf(c_0_138, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r2_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|~r1_orders_2(esk3_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_132, c_0_129])).
% 4.32/4.54  cnf(c_0_139, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))),esk1_3(esk3_0,esk4_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_128]), c_0_134])).
% 4.32/4.54  cnf(c_0_140, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk6_0),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|~r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_135, c_0_17])).
% 4.32/4.54  cnf(c_0_141, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_100]), c_0_17])]), c_0_125])).
% 4.32/4.54  cnf(c_0_142, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_102]), c_0_17])]), c_0_125])).
% 4.32/4.54  cnf(c_0_143, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r2_lattice3(esk3_0,k1_tarski(X1),esk1_3(esk3_0,esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_128]), c_0_18])])).
% 4.32/4.54  cnf(c_0_144, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,esk6_0))|~r2_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 4.32/4.54  cnf(c_0_145, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk6_0),k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_140, c_0_141])).
% 4.32/4.54  cnf(c_0_146, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_142]), c_0_129])).
% 4.32/4.54  cnf(c_0_147, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|~r2_lattice3(esk3_0,k1_tarski(esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_143, c_0_17])).
% 4.32/4.54  cnf(c_0_148, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k1_tarski(esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 4.32/4.54  cnf(c_0_149, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|~r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_128])).
% 4.32/4.54  cnf(c_0_150, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_146, c_0_134])).
% 4.32/4.54  cnf(c_0_151, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_147, c_0_148])).
% 4.32/4.54  cnf(c_0_152, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 4.32/4.54  cnf(c_0_153, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_151])).
% 4.32/4.54  cnf(c_0_154, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_152])).
% 4.32/4.54  cnf(c_0_155, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_153]), c_0_100])).
% 4.32/4.54  cnf(c_0_156, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_154]), c_0_102])).
% 4.32/4.54  cnf(c_0_157, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,X1,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))|~r1_lattice3(esk3_0,X2,X1)|~r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_155]), c_0_18])])).
% 4.32/4.54  cnf(c_0_158, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_104, c_0_156])).
% 4.32/4.54  cnf(c_0_159, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0))|~r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_107]), c_0_17])])).
% 4.32/4.54  cnf(c_0_160, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_hidden(esk1_3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_158, c_0_20])).
% 4.32/4.54  cnf(c_0_161, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_64])).
% 4.32/4.54  cnf(c_0_162, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))))|~m1_subset_1(k2_yellow_0(esk3_0,esk7_4(esk4_0,esk3_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_161])).
% 4.32/4.54  cnf(c_0_163, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_98]), c_0_27]), c_0_64])).
% 4.32/4.54  cnf(c_0_164, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_163]), c_0_17])]), c_0_125])).
% 4.32/4.54  cnf(c_0_165, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,X1,esk6_0)|~r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_164]), c_0_129])).
% 4.32/4.54  cnf(c_0_166, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_165, c_0_134])).
% 4.32/4.54  cnf(c_0_167, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk6_0,esk1_3(esk3_0,esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_149, c_0_166])).
% 4.32/4.54  fof(c_0_168, plain, ![X6]:~v1_xboole_0(k1_tarski(X6)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 4.32/4.54  cnf(c_0_169, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_lattice3(esk3_0,esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_167])).
% 4.32/4.54  cnf(c_0_170, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_168])).
% 4.32/4.54  cnf(c_0_171, negated_conjecture, (k1_tarski(esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_169]), c_0_163])).
% 4.32/4.54  cnf(c_0_172, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 4.32/4.54  cnf(c_0_173, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_171]), c_0_172])]), ['proof']).
% 4.32/4.54  # SZS output end CNFRefutation
% 4.32/4.54  # Proof object total steps             : 174
% 4.32/4.54  # Proof object clause steps            : 149
% 4.32/4.54  # Proof object formula steps           : 25
% 4.32/4.54  # Proof object conjectures             : 119
% 4.32/4.54  # Proof object clause conjectures      : 116
% 4.32/4.54  # Proof object formula conjectures     : 3
% 4.32/4.54  # Proof object initial clauses used    : 29
% 4.32/4.54  # Proof object initial formulas used   : 11
% 4.32/4.54  # Proof object generating inferences   : 118
% 4.32/4.54  # Proof object simplifying inferences  : 104
% 4.32/4.54  # Training examples: 0 positive, 0 negative
% 4.32/4.54  # Parsed axioms                        : 13
% 4.32/4.54  # Removed by relevancy pruning/SinE    : 0
% 4.32/4.54  # Initial clauses                      : 40
% 4.32/4.54  # Removed in clause preprocessing      : 0
% 4.32/4.54  # Initial clauses in saturation        : 40
% 4.32/4.54  # Processed clauses                    : 10155
% 4.32/4.54  # ...of these trivial                  : 0
% 4.32/4.54  # ...subsumed                          : 3813
% 4.32/4.54  # ...remaining for further processing  : 6342
% 4.32/4.54  # Other redundant clauses eliminated   : 2
% 4.32/4.54  # Clauses deleted for lack of memory   : 0
% 4.32/4.54  # Backward-subsumed                    : 3294
% 4.32/4.54  # Backward-rewritten                   : 2331
% 4.32/4.54  # Generated clauses                    : 117721
% 4.32/4.54  # ...of the previous two non-trivial   : 114558
% 4.32/4.54  # Contextual simplify-reflections      : 1009
% 4.32/4.54  # Paramodulations                      : 117719
% 4.32/4.54  # Factorizations                       : 0
% 4.32/4.54  # Equation resolutions                 : 2
% 4.32/4.54  # Propositional unsat checks           : 0
% 4.32/4.54  #    Propositional check models        : 0
% 4.32/4.54  #    Propositional check unsatisfiable : 0
% 4.32/4.54  #    Propositional clauses             : 0
% 4.32/4.54  #    Propositional clauses after purity: 0
% 4.32/4.54  #    Propositional unsat core size     : 0
% 4.32/4.54  #    Propositional preprocessing time  : 0.000
% 4.32/4.54  #    Propositional encoding time       : 0.000
% 4.32/4.54  #    Propositional solver time         : 0.000
% 4.32/4.54  #    Success case prop preproc time    : 0.000
% 4.32/4.54  #    Success case prop encoding time   : 0.000
% 4.32/4.54  #    Success case prop solver time     : 0.000
% 4.32/4.54  # Current number of processed clauses  : 675
% 4.32/4.54  #    Positive orientable unit clauses  : 14
% 4.32/4.54  #    Positive unorientable unit clauses: 0
% 4.32/4.54  #    Negative unit clauses             : 2
% 4.32/4.54  #    Non-unit-clauses                  : 659
% 4.32/4.54  # Current number of unprocessed clauses: 101312
% 4.32/4.54  # ...number of literals in the above   : 623715
% 4.32/4.54  # Current number of archived formulas  : 0
% 4.32/4.54  # Current number of archived clauses   : 5665
% 4.32/4.54  # Clause-clause subsumption calls (NU) : 4020592
% 4.32/4.54  # Rec. Clause-clause subsumption calls : 380444
% 4.32/4.54  # Non-unit clause-clause subsumptions  : 8116
% 4.32/4.54  # Unit Clause-clause subsumption calls : 396
% 4.32/4.54  # Rewrite failures with RHS unbound    : 0
% 4.32/4.54  # BW rewrite match attempts            : 9
% 4.32/4.54  # BW rewrite match successes           : 1
% 4.32/4.54  # Condensation attempts                : 0
% 4.32/4.54  # Condensation successes               : 0
% 4.32/4.54  # Termbank termtop insertions          : 5589904
% 4.38/4.55  
% 4.38/4.55  # -------------------------------------------------
% 4.38/4.55  # User time                : 4.135 s
% 4.38/4.55  # System time              : 0.064 s
% 4.38/4.55  # Total time               : 4.199 s
% 4.38/4.55  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

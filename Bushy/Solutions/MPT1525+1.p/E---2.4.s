%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t3_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:41 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 984 expanded)
%              Number of clauses        :   41 ( 412 expanded)
%              Number of leaves         :    7 ( 232 expanded)
%              Depth                    :   13
%              Number of atoms          :  274 (3799 expanded)
%              Number of equality atoms :   54 ( 984 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t3_yellow_0.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t3_yellow_0.p',dt_u1_orders_2)).

fof(t3_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & v3_lattice3(X1) )
           => v3_lattice3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t3_yellow_0.p',t3_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t3_yellow_0.p',t3_subset)).

fof(t1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X4 = X6 )
                             => ( ( r1_orders_2(X1,X3,X4)
                                 => r1_orders_2(X2,X5,X6) )
                                & ( r2_orders_2(X1,X3,X4)
                                 => r2_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t3_yellow_0.p',t1_yellow_0)).

fof(d12_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r2_lattice3(X1,X2,X3)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t3_yellow_0.p',d12_lattice3)).

fof(t2_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3,X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X2))
                   => ( X4 = X5
                     => ( ( r2_lattice3(X1,X3,X4)
                         => r2_lattice3(X2,X3,X5) )
                        & ( r1_lattice3(X1,X3,X4)
                         => r1_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t3_yellow_0.p',t2_yellow_0)).

fof(c_0_7,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X25 = X27
        | g1_orders_2(X25,X26) != g1_orders_2(X27,X28)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) )
      & ( X26 = X28
        | g1_orders_2(X25,X26) != g1_orders_2(X27,X28)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_8,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | m1_subset_1(u1_orders_2(X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X20)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & v3_lattice3(X1) )
             => v3_lattice3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow_0])).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & v3_lattice3(esk1_0)
    & ~ v3_lattice3(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X43,k1_zfmisc_1(X44))
        | r1_tarski(X43,X44) )
      & ( ~ r1_tarski(X43,X44)
        | m1_subset_1(X43,k1_zfmisc_1(X44)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( u1_orders_2(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

fof(c_0_19,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( ~ r1_orders_2(X32,X34,X35)
        | r1_orders_2(X33,X36,X37)
        | X34 != X36
        | X35 != X37
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | g1_orders_2(u1_struct_0(X32),u1_orders_2(X32)) != g1_orders_2(u1_struct_0(X33),u1_orders_2(X33))
        | ~ l1_orders_2(X33)
        | ~ l1_orders_2(X32) )
      & ( ~ r2_orders_2(X32,X34,X35)
        | r2_orders_2(X33,X36,X37)
        | X34 != X36
        | X35 != X37
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | g1_orders_2(u1_struct_0(X32),u1_orders_2(X32)) != g1_orders_2(u1_struct_0(X33),u1_orders_2(X33))
        | ~ l1_orders_2(X33)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_yellow_0])])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(u1_orders_2(X1),k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( u1_orders_2(esk1_0) = u1_orders_2(esk2_0) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_orders_2(X4,X5,X6)
    | ~ r1_orders_2(X1,X2,X3)
    | X2 != X5
    | X3 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X10,X11,X13,X15] :
      ( ( m1_subset_1(esk3_2(X10,X11),u1_struct_0(X10))
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X11,esk3_2(X10,X11))
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X13)
        | r1_orders_2(X10,esk3_2(X10,X11),X13)
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk5_2(X10,X15),u1_struct_0(X10))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,esk4_1(X10),X15)
        | v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,esk4_1(X10),esk5_2(X10,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,esk4_1(X10),X15)
        | v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X15,esk5_2(X10,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,esk4_1(X10),X15)
        | v3_lattice3(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(u1_orders_2(esk2_0),k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_23])).

fof(c_0_29,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( ( ~ r2_lattice3(X38,X40,X41)
        | r2_lattice3(X39,X40,X42)
        | X41 != X42
        | ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | g1_orders_2(u1_struct_0(X38),u1_orders_2(X38)) != g1_orders_2(u1_struct_0(X39),u1_orders_2(X39))
        | ~ l1_orders_2(X39)
        | ~ l1_orders_2(X38) )
      & ( ~ r1_lattice3(X38,X40,X41)
        | r1_lattice3(X39,X40,X42)
        | X41 != X42
        | ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | g1_orders_2(u1_struct_0(X38),u1_orders_2(X38)) != g1_orders_2(u1_struct_0(X39),u1_orders_2(X39))
        | ~ l1_orders_2(X39)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_yellow_0])])])])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_31,plain,
    ( r1_orders_2(X2,esk3_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_lattice3(X4,X2,X5)
    | ~ r2_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,esk3_2(X2,X3),X4)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(X2,X3,X4)
    | ~ m1_subset_1(esk3_2(X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,plain,
    ( r2_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r2_lattice3(X1,X2,esk3_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(X1,esk3_2(esk1_0,X2),X3)
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(esk1_0,X2,X3)
    | ~ m1_subset_1(esk3_2(esk1_0,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_23]),c_0_36]),c_0_36]),c_0_37]),c_0_16])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_2(esk1_0,X1),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_36]),c_0_37]),c_0_16])])).

cnf(c_0_42,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( r2_lattice3(X1,esk4_1(X1),esk5_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk4_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk4_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,plain,
    ( r2_lattice3(X1,X2,esk3_2(X3,X2))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ m1_subset_1(esk3_2(X3,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_32])).

cnf(c_0_46,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk5_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk4_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_2(esk1_0,X1),X2)
    | ~ r2_lattice3(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v3_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,plain,
    ( r2_lattice3(X1,esk4_1(X2),esk5_2(X2,X3))
    | v3_lattice3(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(X2,esk4_1(X2),X3)
    | ~ m1_subset_1(esk5_2(X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(X1,X2,esk3_2(esk1_0,X2))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ m1_subset_1(esk3_2(esk1_0,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_36]),c_0_37]),c_0_16])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,X1,esk5_2(esk2_0,esk3_2(esk1_0,X1)))
    | ~ r2_lattice3(esk2_0,esk4_1(esk2_0),esk3_2(esk1_0,X1))
    | ~ m1_subset_1(esk5_2(esk2_0,esk3_2(esk1_0,X1)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_41]),c_0_42])]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_lattice3(esk1_0,esk4_1(X1),esk5_2(X1,X2))
    | v3_lattice3(X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    | ~ r2_lattice3(X1,esk4_1(X1),X2)
    | ~ m1_subset_1(esk5_2(X1,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_36]),c_0_36]),c_0_16])])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk3_2(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_41]),c_0_42])])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(esk5_2(esk2_0,esk3_2(esk1_0,esk4_1(esk2_0))),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_41]),c_0_42])]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_44]),c_0_53]),c_0_41]),c_0_42])]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------

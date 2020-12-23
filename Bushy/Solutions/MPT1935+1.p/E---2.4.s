%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t33_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:55 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 (3630 expanded)
%              Number of clauses        :   62 (1246 expanded)
%              Number of leaves         :    5 ( 867 expanded)
%              Depth                    :   18
%              Number of atoms          :  386 (41773 expanded)
%              Number of equality atoms :   24 (1300 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   49 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_yellow_6,conjecture,(
    ! [X1,X2] :
      ( l1_struct_0(X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v1_partfun1(X3,X1) )
         => ( m3_yellow_6(X3,X1,X2)
          <=> ! [X4] :
                ( r2_hidden(X4,X1)
               => ( ~ v2_struct_0(k1_funct_1(X3,X4))
                  & v4_orders_2(k1_funct_1(X3,X4))
                  & v7_waybel_0(k1_funct_1(X3,X4))
                  & l1_waybel_0(k1_funct_1(X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',t33_yellow_6)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',d5_funct_1)).

fof(d15_yellow_6,axiom,(
    ! [X1,X2] :
      ( l1_struct_0(X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v1_partfun1(X3,X1) )
         => ( m3_yellow_6(X3,X1,X2)
          <=> ! [X4] :
                ( r2_hidden(X4,k2_relat_1(X3))
               => ( ~ v2_struct_0(X4)
                  & v4_orders_2(X4)
                  & v7_waybel_0(X4)
                  & l1_waybel_0(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',d15_yellow_6)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',d4_partfun1)).

fof(dt_m3_yellow_6,axiom,(
    ! [X1,X2] :
      ( l1_struct_0(X2)
     => ! [X3] :
          ( m3_yellow_6(X3,X1,X2)
         => ( v1_relat_1(X3)
            & v4_relat_1(X3,X1)
            & v1_funct_1(X3)
            & v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',dt_m3_yellow_6)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( l1_struct_0(X2)
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v4_relat_1(X3,X1)
              & v1_funct_1(X3)
              & v1_partfun1(X3,X1) )
           => ( m3_yellow_6(X3,X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => ( ~ v2_struct_0(k1_funct_1(X3,X4))
                    & v4_orders_2(k1_funct_1(X3,X4))
                    & v7_waybel_0(k1_funct_1(X3,X4))
                    & l1_waybel_0(k1_funct_1(X3,X4),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_yellow_6])).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X23,X24,X25,X27] :
      ( ( r2_hidden(esk6_3(X19,X20,X21),k1_relat_1(X19))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X21 = k1_funct_1(X19,esk6_3(X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(X24,k1_relat_1(X19))
        | X23 != k1_funct_1(X19,X24)
        | r2_hidden(X23,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk7_2(X19,X25),X25)
        | ~ r2_hidden(X27,k1_relat_1(X19))
        | esk7_2(X19,X25) != k1_funct_1(X19,X27)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk8_2(X19,X25),k1_relat_1(X19))
        | r2_hidden(esk7_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( esk7_2(X19,X25) = k1_funct_1(X19,esk8_2(X19,X25))
        | r2_hidden(esk7_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v2_struct_0(X15)
        | ~ r2_hidden(X15,k2_relat_1(X14))
        | ~ m3_yellow_6(X14,X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_partfun1(X14,X12)
        | ~ l1_struct_0(X13) )
      & ( v4_orders_2(X15)
        | ~ r2_hidden(X15,k2_relat_1(X14))
        | ~ m3_yellow_6(X14,X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_partfun1(X14,X12)
        | ~ l1_struct_0(X13) )
      & ( v7_waybel_0(X15)
        | ~ r2_hidden(X15,k2_relat_1(X14))
        | ~ m3_yellow_6(X14,X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_partfun1(X14,X12)
        | ~ l1_struct_0(X13) )
      & ( l1_waybel_0(X15,X13)
        | ~ r2_hidden(X15,k2_relat_1(X14))
        | ~ m3_yellow_6(X14,X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_partfun1(X14,X12)
        | ~ l1_struct_0(X13) )
      & ( r2_hidden(esk5_3(X12,X13,X14),k2_relat_1(X14))
        | m3_yellow_6(X14,X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_partfun1(X14,X12)
        | ~ l1_struct_0(X13) )
      & ( v2_struct_0(esk5_3(X12,X13,X14))
        | ~ v4_orders_2(esk5_3(X12,X13,X14))
        | ~ v7_waybel_0(esk5_3(X12,X13,X14))
        | ~ l1_waybel_0(esk5_3(X12,X13,X14),X13)
        | m3_yellow_6(X14,X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X12)
        | ~ v1_funct_1(X14)
        | ~ v1_partfun1(X14,X12)
        | ~ l1_struct_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_yellow_6])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X9] :
      ( l1_struct_0(esk2_0)
      & v1_relat_1(esk3_0)
      & v4_relat_1(esk3_0,esk1_0)
      & v1_funct_1(esk3_0)
      & v1_partfun1(esk3_0,esk1_0)
      & ( r2_hidden(esk4_0,esk1_0)
        | ~ m3_yellow_6(esk3_0,esk1_0,esk2_0) )
      & ( v2_struct_0(k1_funct_1(esk3_0,esk4_0))
        | ~ v4_orders_2(k1_funct_1(esk3_0,esk4_0))
        | ~ v7_waybel_0(k1_funct_1(esk3_0,esk4_0))
        | ~ l1_waybel_0(k1_funct_1(esk3_0,esk4_0),esk2_0)
        | ~ m3_yellow_6(esk3_0,esk1_0,esk2_0) )
      & ( ~ v2_struct_0(k1_funct_1(esk3_0,X9))
        | ~ r2_hidden(X9,esk1_0)
        | m3_yellow_6(esk3_0,esk1_0,esk2_0) )
      & ( v4_orders_2(k1_funct_1(esk3_0,X9))
        | ~ r2_hidden(X9,esk1_0)
        | m3_yellow_6(esk3_0,esk1_0,esk2_0) )
      & ( v7_waybel_0(k1_funct_1(esk3_0,X9))
        | ~ r2_hidden(X9,esk1_0)
        | m3_yellow_6(esk3_0,esk1_0,esk2_0) )
      & ( l1_waybel_0(k1_funct_1(esk3_0,X9),esk2_0)
        | ~ r2_hidden(X9,esk1_0)
        | m3_yellow_6(esk3_0,esk1_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ( ~ v1_partfun1(X18,X17)
        | k1_relat_1(X18) = X17
        | ~ v1_relat_1(X18)
        | ~ v4_relat_1(X18,X17) )
      & ( k1_relat_1(X18) != X17
        | v1_partfun1(X18,X17)
        | ~ v1_relat_1(X18)
        | ~ v4_relat_1(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))
    | m3_yellow_6(X3,X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X3,X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_partfun1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,X1,esk3_0),k2_relat_1(esk3_0))
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,esk6_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk3_0,X1))
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_3(esk3_0,k2_relat_1(esk3_0),esk5_3(esk1_0,X1,esk3_0)),esk1_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_13]),c_0_15])])).

cnf(c_0_23,plain,
    ( k1_funct_1(X1,esk6_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk3_0,X1))
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | ~ v2_struct_0(k1_funct_1(esk3_0,X1))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk3_0,esk6_3(esk3_0,k2_relat_1(esk3_0),esk5_3(esk1_0,X1,esk3_0))))
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(esk3_0,k2_relat_1(esk3_0),esk5_3(esk1_0,X1,esk3_0))) = esk5_3(esk1_0,X1,esk3_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_13]),c_0_15])])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk3_0,esk6_3(esk3_0,k2_relat_1(esk3_0),esk5_3(esk1_0,X1,esk3_0))))
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ v2_struct_0(k1_funct_1(esk3_0,esk6_3(esk3_0,k2_relat_1(esk3_0),esk5_3(esk1_0,X1,esk3_0))))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk3_0,X1),esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( v2_struct_0(esk5_3(X1,X2,X3))
    | m3_yellow_6(X3,X1,X2)
    | ~ v4_orders_2(esk5_3(X1,X2,X3))
    | ~ v7_waybel_0(esk5_3(X1,X2,X3))
    | ~ l1_waybel_0(esk5_3(X1,X2,X3),X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X3,X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( v7_waybel_0(esk5_3(esk1_0,X1,esk3_0))
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v4_orders_2(esk5_3(esk1_0,X1,esk3_0))
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ v2_struct_0(esk5_3(esk1_0,X1,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk3_0,esk6_3(esk3_0,k2_relat_1(esk3_0),esk5_3(esk1_0,X1,esk3_0))),esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_waybel_0(esk5_3(esk1_0,X1,esk3_0),X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( l1_waybel_0(esk5_3(esk1_0,X1,esk3_0),esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,esk2_0)
    | m3_yellow_6(esk3_0,esk1_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_40,plain,(
    ! [X32,X33,X34] :
      ( ( v1_relat_1(X34)
        | ~ m3_yellow_6(X34,X32,X33)
        | ~ l1_struct_0(X33) )
      & ( v4_relat_1(X34,X32)
        | ~ m3_yellow_6(X34,X32,X33)
        | ~ l1_struct_0(X33) )
      & ( v1_funct_1(X34)
        | ~ m3_yellow_6(X34,X32,X33)
        | ~ l1_struct_0(X33) )
      & ( v1_partfun1(X34,X32)
        | ~ m3_yellow_6(X34,X32,X33)
        | ~ l1_struct_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m3_yellow_6])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0)
    | ~ m3_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( m3_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_44,plain,
    ( v4_orders_2(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X3)
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( v4_relat_1(X1,X2)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v1_funct_1(X1)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v1_partfun1(X1,X2)
    | ~ m3_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),k2_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_13]),c_0_15])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_51,plain,
    ( v4_orders_2(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ l1_struct_0(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk4_0),k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( v7_waybel_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X3)
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk3_0,esk4_0))
    | ~ v4_orders_2(k1_funct_1(esk3_0,esk4_0))
    | ~ v7_waybel_0(k1_funct_1(esk3_0,esk4_0))
    | ~ l1_waybel_0(k1_funct_1(esk3_0,esk4_0),esk2_0)
    | ~ m3_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_55,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk3_0,esk4_0))
    | ~ m3_yellow_6(esk3_0,X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( v7_waybel_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ l1_struct_0(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_53,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_57,plain,
    ( l1_waybel_0(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(X3))
    | ~ m3_yellow_6(X3,X4,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X3,X4)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk3_0,esk4_0))
    | ~ l1_waybel_0(k1_funct_1(esk3_0,esk4_0),esk2_0)
    | ~ v7_waybel_0(k1_funct_1(esk3_0,esk4_0))
    | ~ v4_orders_2(k1_funct_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_43])])).

cnf(c_0_59,negated_conjecture,
    ( v4_orders_2(k1_funct_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_39])])).

cnf(c_0_60,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk3_0,esk4_0))
    | ~ m3_yellow_6(esk3_0,X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_52])).

cnf(c_0_61,plain,
    ( l1_waybel_0(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(X3))
    | ~ m3_yellow_6(X3,X4,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_57,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_62,plain,
    ( ~ v2_struct_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ v1_relat_1(X2)
    | ~ v4_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_partfun1(X2,X3)
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk3_0,esk4_0))
    | ~ l1_waybel_0(k1_funct_1(esk3_0,esk4_0),esk2_0)
    | ~ v7_waybel_0(k1_funct_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( v7_waybel_0(k1_funct_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_43]),c_0_39])])).

cnf(c_0_65,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk3_0,esk4_0),X1)
    | ~ m3_yellow_6(esk3_0,X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_52])).

cnf(c_0_66,plain,
    ( ~ v2_struct_0(X1)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ m3_yellow_6(X2,X3,X4)
    | ~ l1_struct_0(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_62,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk3_0,esk4_0))
    | ~ l1_waybel_0(k1_funct_1(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_68,negated_conjecture,
    ( l1_waybel_0(k1_funct_1(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_43]),c_0_39])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(k1_funct_1(esk3_0,esk4_0))
    | ~ m3_yellow_6(esk3_0,X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_52])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k1_funct_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( ~ m3_yellow_6(esk3_0,X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_43]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------

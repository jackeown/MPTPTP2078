%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t17_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 34.39s
% Output     : CNFRefutation 34.39s
% Verified   : 
% Statistics : Number of formulae       :   86 (3093 expanded)
%              Number of clauses        :   59 (1041 expanded)
%              Number of leaves         :   13 ( 736 expanded)
%              Depth                    :   12
%              Number of atoms          :  799 (19701 expanded)
%              Number of equality atoms :   79 (2300 expanded)
%              Maximal formula depth    :   47 (   6 average)
%              Maximal clause size      :  352 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_lattice3,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',t17_lattice3)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',redefinition_k12_lattice3)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',dt_k12_lattice3)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',commutativity_k12_lattice3)).

fof(commutativity_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',commutativity_k13_lattice3)).

fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',cc2_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',dt_k11_lattice3)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',reflexivity_r3_orders_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',existence_m1_subset_1)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',redefinition_k13_lattice3)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',redefinition_r3_orders_2)).

fof(d13_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ? [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                      & r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X4 = k10_lattice3(X1,X2,X3)
                      <=> ( r1_orders_2(X1,X2,X4)
                          & r1_orders_2(X1,X3,X4)
                          & ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( ( r1_orders_2(X1,X2,X5)
                                  & r1_orders_2(X1,X3,X5) )
                               => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t17_lattice3.p',d13_lattice3)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_lattice3])).

fof(c_0_14,plain,(
    ! [X48,X49,X50] :
      ( ~ v5_orders_2(X48)
      | ~ v2_lattice3(X48)
      | ~ l1_orders_2(X48)
      | ~ m1_subset_1(X49,u1_struct_0(X48))
      | ~ m1_subset_1(X50,u1_struct_0(X48))
      | k12_lattice3(X48,X49,X50) = k11_lattice3(X48,X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_15,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_lattice3(esk1_0)
    & v2_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k13_lattice3(esk1_0,k12_lattice3(esk1_0,esk2_0,esk3_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X31,X32,X33] :
      ( ~ v5_orders_2(X31)
      | ~ v2_lattice3(X31)
      | ~ l1_orders_2(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | m1_subset_1(k12_lattice3(X31,X32,X33),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

cnf(c_0_17,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X11,X12,X13] :
      ( ~ v5_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k12_lattice3(X11,X12,X13) = k12_lattice3(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk3_0) = k11_lattice3(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_26,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk2_0) = k11_lattice3(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23]),c_0_19]),c_0_20]),c_0_21])])).

fof(c_0_28,plain,(
    ! [X14,X15,X16] :
      ( ~ v5_orders_2(X14)
      | ~ v1_lattice3(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | k13_lattice3(X14,X15,X16) = k13_lattice3(X14,X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k13_lattice3])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk1_0,X1,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_19]),c_0_20]),c_0_21])])).

fof(c_0_30,plain,(
    ! [X42,X43,X44,X45,X46] :
      ( ( r1_orders_2(X42,X45,X43)
        | X45 != k11_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v2_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( r1_orders_2(X42,X45,X44)
        | X45 != k11_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v2_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ r1_orders_2(X42,X46,X43)
        | ~ r1_orders_2(X42,X46,X44)
        | r1_orders_2(X42,X46,X45)
        | X45 != k11_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v2_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( m1_subset_1(esk9_4(X42,X43,X44,X45),u1_struct_0(X42))
        | ~ r1_orders_2(X42,X45,X43)
        | ~ r1_orders_2(X42,X45,X44)
        | X45 = k11_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v2_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( r1_orders_2(X42,esk9_4(X42,X43,X44,X45),X43)
        | ~ r1_orders_2(X42,X45,X43)
        | ~ r1_orders_2(X42,X45,X44)
        | X45 = k11_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v2_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( r1_orders_2(X42,esk9_4(X42,X43,X44,X45),X44)
        | ~ r1_orders_2(X42,X45,X43)
        | ~ r1_orders_2(X42,X45,X44)
        | X45 = k11_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v2_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( ~ r1_orders_2(X42,esk9_4(X42,X43,X44,X45),X45)
        | ~ r1_orders_2(X42,X45,X43)
        | ~ r1_orders_2(X42,X45,X44)
        | X45 = k11_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v2_lattice3(X42)
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_31,plain,(
    ! [X69] :
      ( ~ l1_orders_2(X69)
      | ~ v2_lattice3(X69)
      | ~ v2_struct_0(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_32,plain,(
    ! [X28,X29,X30] :
      ( ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | m1_subset_1(k11_lattice3(X28,X29,X30),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_33,plain,(
    ! [X57,X58,X59] :
      ( v2_struct_0(X57)
      | ~ v3_orders_2(X57)
      | ~ l1_orders_2(X57)
      | ~ m1_subset_1(X58,u1_struct_0(X57))
      | ~ m1_subset_1(X59,u1_struct_0(X57))
      | r3_orders_2(X57,X58,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_34,plain,(
    ! [X40] : m1_subset_1(esk8_1(X40),X40) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_35,negated_conjecture,
    ( k13_lattice3(esk1_0,k12_lattice3(esk1_0,esk2_0,esk3_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,esk3_0) = k11_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk3_0) = k12_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_38,negated_conjecture,
    ( k12_lattice3(esk1_0,esk3_0,esk2_0) = k11_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_39,plain,
    ( k13_lattice3(X1,X2,X3) = k13_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k12_lattice3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

fof(c_0_42,plain,(
    ! [X51,X52,X53] :
      ( ~ v5_orders_2(X51)
      | ~ v1_lattice3(X51)
      | ~ l1_orders_2(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | ~ m1_subset_1(X53,u1_struct_0(X51))
      | k13_lattice3(X51,X52,X53) = k10_lattice3(X51,X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_43,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( k13_lattice3(esk1_0,k11_lattice3(esk1_0,esk2_0,esk3_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk3_0) = k11_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_36]),c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k13_lattice3(esk1_0,X1,esk3_0) = k13_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_19]),c_0_40]),c_0_21])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k11_lattice3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_52,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_43,c_0_44])]),c_0_45])).

fof(c_0_54,plain,(
    ! [X54,X55,X56] :
      ( ( ~ r3_orders_2(X54,X55,X56)
        | r1_orders_2(X54,X55,X56)
        | v2_struct_0(X54)
        | ~ v3_orders_2(X54)
        | ~ l1_orders_2(X54)
        | ~ m1_subset_1(X55,u1_struct_0(X54))
        | ~ m1_subset_1(X56,u1_struct_0(X54)) )
      & ( ~ r1_orders_2(X54,X55,X56)
        | r3_orders_2(X54,X55,X56)
        | v2_struct_0(X54)
        | ~ v3_orders_2(X54)
        | ~ l1_orders_2(X54)
        | ~ m1_subset_1(X55,u1_struct_0(X54))
        | ~ m1_subset_1(X56,u1_struct_0(X54)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_55,plain,
    ( r3_orders_2(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( k13_lattice3(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k13_lattice3(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0) = k13_lattice3(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k13_lattice3(esk1_0,X1,esk3_0) = k10_lattice3(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_18]),c_0_19]),c_0_40]),c_0_21])])).

fof(c_0_60,plain,(
    ! [X17,X18,X19,X20,X22,X23] :
      ( ( r1_orders_2(X17,X18,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X23)
        | ~ r1_orders_2(X17,X19,X23)
        | r1_orders_2(X17,X22,X23)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X22,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X18,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X18,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X23)
        | ~ r1_orders_2(X17,X19,X23)
        | r1_orders_2(X17,X22,X23)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X18,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X18,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X18,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X18,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X22,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X18,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X23)
        | ~ r1_orders_2(X17,X19,X23)
        | r1_orders_2(X17,X22,X23)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X22,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,X22)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X23)
        | ~ r1_orders_2(X17,X19,X23)
        | r1_orders_2(X17,X22,X23)
        | X22 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X22,esk5_4(X17,X18,X19,X22))
        | ~ r1_orders_2(X17,X18,X22)
        | ~ r1_orders_2(X17,X19,X22)
        | X22 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_lattice3])])])])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk1_0,k11_lattice3(esk1_0,X1,esk2_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_62,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r3_orders_2(esk1_0,esk3_0,esk3_0)
    | v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_18]),c_0_19]),c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( k13_lattice3(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k13_lattice3(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0)) = k10_lattice3(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_51]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k13_lattice3(esk1_0,X1,k11_lattice3(esk1_0,esk3_0,esk2_0)) = k10_lattice3(esk1_0,X1,k11_lattice3(esk1_0,esk3_0,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_19]),c_0_40]),c_0_21])])).

cnf(c_0_67,plain,
    ( r1_orders_2(X1,X2,esk5_4(X1,X2,X3,X4))
    | X4 = k10_lattice3(X1,X2,X3)
    | r1_orders_2(X1,X2,esk4_4(X1,X2,X3,X5))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | r1_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_18]),c_0_19]),c_0_56])])).

cnf(c_0_70,negated_conjecture,
    ( k10_lattice3(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k10_lattice3(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0) = k10_lattice3(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_18]),c_0_65])).

cnf(c_0_72,plain,
    ( X2 = k10_lattice3(X1,X3,X4)
    | r1_orders_2(X1,X3,esk4_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk5_4(X1,X3,X4,X2))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( r1_orders_2(X1,X2,esk5_4(X1,X2,X3,X4))
    | X4 = k10_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X2,X3,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X5)
    | ~ r1_orders_2(X1,X3,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( X2 = k10_lattice3(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,esk5_4(X1,X3,X4,X2))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,esk4_4(X1,X3,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0))
    | r1_orders_2(esk1_0,X2,esk4_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | r1_orders_2(esk1_0,X2,esk5_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),X1))
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),X1)
    | ~ r1_orders_2(esk1_0,X2,esk3_0)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_18]),c_0_51]),c_0_19]),c_0_21])])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_69]),c_0_19]),c_0_20])])).

cnf(c_0_77,negated_conjecture,
    ( k10_lattice3(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0))
    | r1_orders_2(esk1_0,X2,esk4_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | ~ r1_orders_2(esk1_0,X1,esk5_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),X1))
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),X1)
    | ~ r1_orders_2(esk1_0,X2,esk3_0)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_68]),c_0_18]),c_0_51]),c_0_19]),c_0_21])])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0))
    | r1_orders_2(esk1_0,X2,esk5_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),X1))
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),X1)
    | ~ r1_orders_2(esk1_0,X2,esk3_0)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_68]),c_0_18]),c_0_51]),c_0_19]),c_0_21])])).

cnf(c_0_80,negated_conjecture,
    ( X1 = k10_lattice3(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0))
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | ~ r1_orders_2(esk1_0,X1,esk5_4(esk1_0,X2,k11_lattice3(esk1_0,esk3_0,esk2_0),X1))
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk3_0,esk2_0),X1)
    | ~ r1_orders_2(esk1_0,X2,esk3_0)
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_68]),c_0_18]),c_0_19]),c_0_21])]),c_0_51])])).

cnf(c_0_81,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | r1_orders_2(esk1_0,esk3_0,esk5_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_68]),c_0_76]),c_0_18])]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | ~ r1_orders_2(esk1_0,esk3_0,esk5_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_76]),c_0_68]),c_0_76]),c_0_18])]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk5_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_76]),c_0_68]),c_0_76]),c_0_18])]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,esk4_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0))
    | ~ r1_orders_2(esk1_0,esk3_0,esk5_4(esk1_0,esk3_0,k11_lattice3(esk1_0,esk3_0,esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_76]),c_0_68]),c_0_76]),c_0_18])]),c_0_77])).

cnf(c_0_85,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_81,c_0_82,c_0_83,c_0_84]),
    [proof]).
%------------------------------------------------------------------------------

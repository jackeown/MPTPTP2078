%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t18_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:54 EDT 2019

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :   68 (1326 expanded)
%              Number of clauses        :   47 ( 460 expanded)
%              Number of leaves         :   10 ( 314 expanded)
%              Depth                    :   12
%              Number of atoms          :  740 (9140 expanded)
%              Number of equality atoms :   70 ( 972 expanded)
%              Maximal formula depth    :   47 (   7 average)
%              Maximal clause size      :  352 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_lattice3,conjecture,(
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
             => k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',t18_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',cc2_lattice3)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',dt_k10_lattice3)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',reflexivity_r3_orders_2)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',redefinition_k13_lattice3)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',commutativity_k12_lattice3)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',redefinition_k12_lattice3)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',redefinition_r3_orders_2)).

fof(l26_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k10_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',l26_lattice3)).

fof(d14_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ? [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                      & r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X4 = k11_lattice3(X1,X2,X3)
                      <=> ( r1_orders_2(X1,X4,X2)
                          & r1_orders_2(X1,X4,X3)
                          & ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( ( r1_orders_2(X1,X5,X2)
                                  & r1_orders_2(X1,X5,X3) )
                               => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t18_lattice3.p',d14_lattice3)).

fof(c_0_10,negated_conjecture,(
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
               => k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_lattice3])).

fof(c_0_11,plain,(
    ! [X69] :
      ( ~ l1_orders_2(X69)
      | ~ v2_lattice3(X69)
      | ~ v2_struct_0(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_12,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_lattice3(esk1_0)
    & v2_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k12_lattice3(esk1_0,esk2_0,k13_lattice3(esk1_0,esk2_0,esk3_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | m1_subset_1(k10_lattice3(X25,X26,X27),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

fof(c_0_16,plain,(
    ! [X57,X58,X59] :
      ( v2_struct_0(X57)
      | ~ v3_orders_2(X57)
      | ~ l1_orders_2(X57)
      | ~ m1_subset_1(X58,u1_struct_0(X57))
      | ~ m1_subset_1(X59,u1_struct_0(X57))
      | r3_orders_2(X57,X58,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    | ~ l1_orders_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X51,X52,X53] :
      ( ~ v5_orders_2(X51)
      | ~ v1_lattice3(X51)
      | ~ l1_orders_2(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | ~ m1_subset_1(X53,u1_struct_0(X51))
      | k13_lattice3(X51,X52,X53) = k10_lattice3(X51,X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_20,plain,(
    ! [X11,X12,X13] :
      ( ~ v5_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k12_lattice3(X11,X12,X13) = k12_lattice3(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_26,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_29,plain,(
    ! [X48,X49,X50] :
      ( ~ v5_orders_2(X48)
      | ~ v2_lattice3(X48)
      | ~ l1_orders_2(X48)
      | ~ m1_subset_1(X49,u1_struct_0(X48))
      | ~ m1_subset_1(X50,u1_struct_0(X48))
      | k12_lattice3(X48,X49,X50) = k11_lattice3(X48,X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_30,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k10_lattice3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18])])).

fof(c_0_33,plain,(
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

cnf(c_0_34,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_18]),c_0_24])]),c_0_25])).

fof(c_0_35,plain,(
    ! [X42,X43,X44,X45,X46] :
      ( ( r1_orders_2(X42,X43,X45)
        | X45 != k10_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v1_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( r1_orders_2(X42,X44,X45)
        | X45 != k10_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v1_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ r1_orders_2(X42,X43,X46)
        | ~ r1_orders_2(X42,X44,X46)
        | r1_orders_2(X42,X45,X46)
        | X45 != k10_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v1_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( m1_subset_1(esk9_4(X42,X43,X44,X45),u1_struct_0(X42))
        | ~ r1_orders_2(X42,X43,X45)
        | ~ r1_orders_2(X42,X44,X45)
        | X45 = k10_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v1_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( r1_orders_2(X42,X43,esk9_4(X42,X43,X44,X45))
        | ~ r1_orders_2(X42,X43,X45)
        | ~ r1_orders_2(X42,X44,X45)
        | X45 = k10_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v1_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( r1_orders_2(X42,X44,esk9_4(X42,X43,X44,X45))
        | ~ r1_orders_2(X42,X43,X45)
        | ~ r1_orders_2(X42,X44,X45)
        | X45 = k10_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v1_lattice3(X42)
        | ~ l1_orders_2(X42) )
      & ( ~ r1_orders_2(X42,X45,esk9_4(X42,X43,X44,X45))
        | ~ r1_orders_2(X42,X43,X45)
        | ~ r1_orders_2(X42,X44,X45)
        | X45 = k10_lattice3(X42,X43,X44)
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v5_orders_2(X42)
        | ~ v1_lattice3(X42)
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( k13_lattice3(esk1_0,X1,esk3_0) = k10_lattice3(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_18]),c_0_27]),c_0_28])])).

cnf(c_0_37,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk2_0) = k12_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_18]),c_0_14]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k10_lattice3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_40,plain,(
    ! [X17,X18,X19,X20,X22,X23] :
      ( ( r1_orders_2(X17,X22,X18)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X22,X19)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X23,X18)
        | ~ r1_orders_2(X17,X23,X19)
        | r1_orders_2(X17,X23,X22)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X18)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X19)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X22)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X22,X18)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X22,X19)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X23,X18)
        | ~ r1_orders_2(X17,X23,X19)
        | r1_orders_2(X17,X23,X22)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X18)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X19)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X22)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X22,X18)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X22,X19)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X23,X18)
        | ~ r1_orders_2(X17,X23,X19)
        | r1_orders_2(X17,X23,X22)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X18)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X19)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X22)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X22,X18)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X22,X19)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X23,X18)
        | ~ r1_orders_2(X17,X23,X19)
        | r1_orders_2(X17,X23,X22)
        | X22 != k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_4(X17,X18,X19,X22),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X18)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X19)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,esk5_4(X17,X18,X19,X22),X22)
        | ~ r1_orders_2(X17,X22,X18)
        | ~ r1_orders_2(X17,X22,X19)
        | X22 = k11_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X17))
        | ~ r1_orders_2(X17,esk4_4(X17,X18,X19,X20),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X20,X18)
        | ~ r1_orders_2(X17,X20,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_lattice3])])])])])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r3_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_43,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,k13_lattice3(esk1_0,esk2_0,esk3_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k13_lattice3(esk1_0,esk2_0,esk3_0) = k10_lattice3(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,esk2_0) = k11_lattice3(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_18]),c_0_14]),c_0_28])])).

cnf(c_0_47,negated_conjecture,
    ( k12_lattice3(esk1_0,k10_lattice3(esk1_0,esk2_0,esk3_0),esk2_0) = k12_lattice3(esk1_0,esk2_0,k10_lattice3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X5),X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_31]),c_0_18]),c_0_24])]),c_0_25])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,k10_lattice3(esk1_0,esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k12_lattice3(esk1_0,esk2_0,k10_lattice3(esk1_0,esk2_0,esk3_0)) = k11_lattice3(esk1_0,k10_lattice3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_39]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k12_lattice3(esk1_0,X1,k10_lattice3(esk1_0,esk2_0,esk3_0)) = k11_lattice3(esk1_0,X1,k10_lattice3(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_39]),c_0_18]),c_0_14]),c_0_28])])).

cnf(c_0_54,plain,
    ( r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk4_4(X1,X2,X3,X5),X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk4_4(X1,X2,X3,X5),X3)
    | ~ r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k11_lattice3(esk1_0,X2,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X2,esk2_0,esk2_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk5_4(esk1_0,X2,esk2_0,X1),X1)
    | ~ r1_orders_2(esk1_0,esk2_0,X2)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_31]),c_0_18]),c_0_28])])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,k10_lattice3(esk1_0,X1,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_22]),c_0_18]),c_0_27]),c_0_28])]),c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( k11_lattice3(esk1_0,k10_lattice3(esk1_0,esk2_0,esk3_0),esk2_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k11_lattice3(esk1_0,k10_lattice3(esk1_0,esk2_0,esk3_0),esk2_0) = k11_lattice3(esk1_0,esk2_0,k10_lattice3(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_31]),c_0_52])).

cnf(c_0_60,plain,
    ( r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk4_4(X1,X2,X3,X5),X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k11_lattice3(esk1_0,X2,esk2_0)
    | r1_orders_2(esk1_0,esk5_4(esk1_0,X2,esk2_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_4(esk1_0,X2,esk2_0,esk2_0),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X2)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_49]),c_0_31]),c_0_18]),c_0_28])])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k11_lattice3(esk1_0,X2,esk2_0)
    | ~ r1_orders_2(esk1_0,esk5_4(esk1_0,X2,esk2_0,X1),X1)
    | ~ r1_orders_2(esk1_0,esk2_0,X2)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_49]),c_0_31]),c_0_18]),c_0_28])]),c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,k10_lattice3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_31])).

cnf(c_0_64,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,k10_lattice3(esk1_0,esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k11_lattice3(esk1_0,X2,esk2_0)
    | r1_orders_2(esk1_0,esk5_4(esk1_0,X2,esk2_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X2)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_31]),c_0_18]),c_0_28])]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk5_4(esk1_0,k10_lattice3(esk1_0,esk2_0,esk3_0),esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_59]),c_0_63]),c_0_49]),c_0_31]),c_0_39])]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_63]),c_0_59]),c_0_63]),c_0_49]),c_0_31]),c_0_39])]),c_0_64]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------

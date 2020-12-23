%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:34 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 298 expanded)
%              Number of clauses        :   36 ( 103 expanded)
%              Number of leaves         :    8 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  276 (2274 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_waybel_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_waybel_0(X3,X1) )
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X1)
                    & l1_waybel_0(X4,X1) )
                 => ( X4 = k3_waybel_2(X1,X2,X3)
                  <=> ( g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X4))
                         => ? [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                              & X6 = k1_funct_1(u1_waybel_0(X1,X3),X5)
                              & k1_funct_1(u1_waybel_0(X1,X4),X5) = k11_lattice3(X1,X2,X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_2)).

fof(dt_k3_waybel_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X1) )
     => ( v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)
        & l1_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_2)).

fof(t10_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v4_orders_2(X3)
                & v7_waybel_0(X3)
                & l1_waybel_0(X3,X1) )
             => ( ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
                & v4_orders_2(k3_waybel_2(X1,X2,X3))
                & v7_waybel_0(k3_waybel_2(X1,X2,X3))
                & l1_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_9)).

fof(fc5_waybel_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X1) )
     => ( ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
        & v6_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_waybel_2)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(l16_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( v4_orders_2(X1)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l16_yellow_6)).

fof(l15_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( v7_waybel_0(X1)
      <=> v7_waybel_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l15_yellow_6)).

fof(c_0_8,plain,(
    ! [X34,X35,X36,X37,X38,X41] :
      ( ( g1_orders_2(u1_struct_0(X37),u1_orders_2(X37)) = g1_orders_2(u1_struct_0(X36),u1_orders_2(X36))
        | X37 != k3_waybel_2(X34,X35,X36)
        | ~ v6_waybel_0(X37,X34)
        | ~ l1_waybel_0(X37,X34)
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) )
      & ( m1_subset_1(esk4_5(X34,X35,X36,X37,X38),u1_struct_0(X34))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | X37 != k3_waybel_2(X34,X35,X36)
        | ~ v6_waybel_0(X37,X34)
        | ~ l1_waybel_0(X37,X34)
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) )
      & ( esk4_5(X34,X35,X36,X37,X38) = k1_funct_1(u1_waybel_0(X34,X36),X38)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | X37 != k3_waybel_2(X34,X35,X36)
        | ~ v6_waybel_0(X37,X34)
        | ~ l1_waybel_0(X37,X34)
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) )
      & ( k1_funct_1(u1_waybel_0(X34,X37),X38) = k11_lattice3(X34,X35,esk4_5(X34,X35,X36,X37,X38))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | X37 != k3_waybel_2(X34,X35,X36)
        | ~ v6_waybel_0(X37,X34)
        | ~ l1_waybel_0(X37,X34)
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) )
      & ( m1_subset_1(esk5_4(X34,X35,X36,X37),u1_struct_0(X37))
        | g1_orders_2(u1_struct_0(X37),u1_orders_2(X37)) != g1_orders_2(u1_struct_0(X36),u1_orders_2(X36))
        | X37 = k3_waybel_2(X34,X35,X36)
        | ~ v6_waybel_0(X37,X34)
        | ~ l1_waybel_0(X37,X34)
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) )
      & ( ~ m1_subset_1(X41,u1_struct_0(X34))
        | X41 != k1_funct_1(u1_waybel_0(X34,X36),esk5_4(X34,X35,X36,X37))
        | k1_funct_1(u1_waybel_0(X34,X37),esk5_4(X34,X35,X36,X37)) != k11_lattice3(X34,X35,X41)
        | g1_orders_2(u1_struct_0(X37),u1_orders_2(X37)) != g1_orders_2(u1_struct_0(X36),u1_orders_2(X36))
        | X37 = k3_waybel_2(X34,X35,X36)
        | ~ v6_waybel_0(X37,X34)
        | ~ l1_waybel_0(X37,X34)
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_waybel_2])])])])])])).

fof(c_0_9,plain,(
    ! [X42,X43,X44] :
      ( ( v6_waybel_0(k3_waybel_2(X42,X43,X44),X42)
        | v2_struct_0(X42)
        | ~ l1_orders_2(X42)
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X44)
        | ~ l1_waybel_0(X44,X42) )
      & ( l1_waybel_0(k3_waybel_2(X42,X43,X44),X42)
        | v2_struct_0(X42)
        | ~ l1_orders_2(X42)
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X44)
        | ~ l1_waybel_0(X44,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_waybel_2])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v4_orders_2(X3)
                  & v7_waybel_0(X3)
                  & l1_waybel_0(X3,X1) )
               => ( ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
                  & v4_orders_2(k3_waybel_2(X1,X2,X3))
                  & v7_waybel_0(k3_waybel_2(X1,X2,X3))
                  & l1_waybel_0(k3_waybel_2(X1,X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_waybel_9])).

cnf(c_0_11,plain,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | X1 != k3_waybel_2(X3,X4,X2)
    | ~ v6_waybel_0(X1,X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( l1_waybel_0(k3_waybel_2(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & ~ v2_struct_0(esk8_0)
    & v4_orders_2(esk8_0)
    & v7_waybel_0(esk8_0)
    & l1_waybel_0(esk8_0,esk6_0)
    & ( v2_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))
      | ~ v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))
      | ~ v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))
      | ~ l1_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_15,plain,(
    ! [X45,X46,X47] :
      ( ( ~ v2_struct_0(k3_waybel_2(X45,X46,X47))
        | v2_struct_0(X45)
        | ~ l1_orders_2(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X47)
        | ~ l1_waybel_0(X47,X45) )
      & ( v6_waybel_0(k3_waybel_2(X45,X46,X47),X45)
        | v2_struct_0(X45)
        | ~ l1_orders_2(X45)
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X47)
        | ~ l1_waybel_0(X47,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_waybel_2])])])])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ l1_struct_0(X10)
      | ~ l1_waybel_0(X11,X10)
      | l1_orders_2(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

fof(c_0_17,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_18,plain,
    ( g1_orders_2(u1_struct_0(k3_waybel_2(X1,X2,X3)),u1_orders_2(k3_waybel_2(X1,X2,X3))) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k3_waybel_2(X1,X2,X3))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X30] :
      ( ( ~ v4_orders_2(X30)
        | v4_orders_2(g1_orders_2(u1_struct_0(X30),u1_orders_2(X30)))
        | v2_struct_0(X30)
        | ~ l1_orders_2(X30) )
      & ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X30),u1_orders_2(X30)))
        | v4_orders_2(X30)
        | v2_struct_0(X30)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l16_yellow_6])])])])).

cnf(c_0_27,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_waybel_2(esk6_0,X1,esk8_0)),u1_orders_2(k3_waybel_2(esk6_0,X1,esk8_0))) = g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ v2_struct_0(k3_waybel_2(esk6_0,X1,esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( l1_orders_2(k3_waybel_2(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_25])).

cnf(c_0_31,plain,
    ( v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0)),u1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))) = g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( l1_orders_2(k3_waybel_2(esk6_0,X1,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20])]),c_0_22]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))
    | ~ v4_orders_2(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)))
    | ~ l1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( l1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( l1_orders_2(esk8_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

fof(c_0_38,plain,(
    ! [X29] :
      ( ( ~ v7_waybel_0(X29)
        | v7_waybel_0(g1_orders_2(u1_struct_0(X29),u1_orders_2(X29)))
        | v2_struct_0(X29)
        | ~ l1_orders_2(X29) )
      & ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(X29),u1_orders_2(X29)))
        | v7_waybel_0(X29)
        | v2_struct_0(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l15_yellow_6])])])])).

cnf(c_0_39,negated_conjecture,
    ( v2_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))
    | ~ v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))
    | ~ v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))
    | ~ l1_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))
    | ~ v4_orders_2(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,plain,
    ( v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_20])])).

cnf(c_0_44,plain,
    ( v7_waybel_0(X1)
    | v2_struct_0(X1)
    | ~ v7_waybel_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( ~ v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))
    | ~ v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_12]),c_0_28]),c_0_19]),c_0_20])]),c_0_33]),c_0_21]),c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])]),c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))
    | ~ v7_waybel_0(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)))
    | ~ l1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( ~ v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_36])]),c_0_48])).

cnf(c_0_50,plain,
    ( v7_waybel_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_43])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.21/0.44  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.031 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(d3_waybel_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((~(v2_struct_0(X3))&l1_waybel_0(X3,X1))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k3_waybel_2(X1,X2,X3)<=>(g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X4))=>?[X6]:((m1_subset_1(X6,u1_struct_0(X1))&X6=k1_funct_1(u1_waybel_0(X1,X3),X5))&k1_funct_1(u1_waybel_0(X1,X4),X5)=k11_lattice3(X1,X2,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_waybel_2)).
% 0.21/0.44  fof(dt_k3_waybel_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&~(v2_struct_0(X3)))&l1_waybel_0(X3,X1))=>(v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)&l1_waybel_0(k3_waybel_2(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_waybel_2)).
% 0.21/0.44  fof(t10_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((~(v2_struct_0(k3_waybel_2(X1,X2,X3)))&v4_orders_2(k3_waybel_2(X1,X2,X3)))&v7_waybel_0(k3_waybel_2(X1,X2,X3)))&l1_waybel_0(k3_waybel_2(X1,X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_9)).
% 0.21/0.44  fof(fc5_waybel_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&~(v2_struct_0(X3)))&l1_waybel_0(X3,X1))=>(~(v2_struct_0(k3_waybel_2(X1,X2,X3)))&v6_waybel_0(k3_waybel_2(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_waybel_2)).
% 0.21/0.44  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.21/0.44  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.21/0.44  fof(l16_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>(v4_orders_2(X1)<=>v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l16_yellow_6)).
% 0.21/0.44  fof(l15_yellow_6, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>(v7_waybel_0(X1)<=>v7_waybel_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l15_yellow_6)).
% 0.21/0.44  fof(c_0_8, plain, ![X34, X35, X36, X37, X38, X41]:(((g1_orders_2(u1_struct_0(X37),u1_orders_2(X37))=g1_orders_2(u1_struct_0(X36),u1_orders_2(X36))|X37!=k3_waybel_2(X34,X35,X36)|(~v6_waybel_0(X37,X34)|~l1_waybel_0(X37,X34))|(v2_struct_0(X36)|~l1_waybel_0(X36,X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34)))&(((m1_subset_1(esk4_5(X34,X35,X36,X37,X38),u1_struct_0(X34))|~m1_subset_1(X38,u1_struct_0(X37))|X37!=k3_waybel_2(X34,X35,X36)|(~v6_waybel_0(X37,X34)|~l1_waybel_0(X37,X34))|(v2_struct_0(X36)|~l1_waybel_0(X36,X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34)))&(esk4_5(X34,X35,X36,X37,X38)=k1_funct_1(u1_waybel_0(X34,X36),X38)|~m1_subset_1(X38,u1_struct_0(X37))|X37!=k3_waybel_2(X34,X35,X36)|(~v6_waybel_0(X37,X34)|~l1_waybel_0(X37,X34))|(v2_struct_0(X36)|~l1_waybel_0(X36,X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34))))&(k1_funct_1(u1_waybel_0(X34,X37),X38)=k11_lattice3(X34,X35,esk4_5(X34,X35,X36,X37,X38))|~m1_subset_1(X38,u1_struct_0(X37))|X37!=k3_waybel_2(X34,X35,X36)|(~v6_waybel_0(X37,X34)|~l1_waybel_0(X37,X34))|(v2_struct_0(X36)|~l1_waybel_0(X36,X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34)))))&((m1_subset_1(esk5_4(X34,X35,X36,X37),u1_struct_0(X37))|g1_orders_2(u1_struct_0(X37),u1_orders_2(X37))!=g1_orders_2(u1_struct_0(X36),u1_orders_2(X36))|X37=k3_waybel_2(X34,X35,X36)|(~v6_waybel_0(X37,X34)|~l1_waybel_0(X37,X34))|(v2_struct_0(X36)|~l1_waybel_0(X36,X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34)))&(~m1_subset_1(X41,u1_struct_0(X34))|X41!=k1_funct_1(u1_waybel_0(X34,X36),esk5_4(X34,X35,X36,X37))|k1_funct_1(u1_waybel_0(X34,X37),esk5_4(X34,X35,X36,X37))!=k11_lattice3(X34,X35,X41)|g1_orders_2(u1_struct_0(X37),u1_orders_2(X37))!=g1_orders_2(u1_struct_0(X36),u1_orders_2(X36))|X37=k3_waybel_2(X34,X35,X36)|(~v6_waybel_0(X37,X34)|~l1_waybel_0(X37,X34))|(v2_struct_0(X36)|~l1_waybel_0(X36,X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~l1_orders_2(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_waybel_2])])])])])])).
% 0.21/0.44  fof(c_0_9, plain, ![X42, X43, X44]:((v6_waybel_0(k3_waybel_2(X42,X43,X44),X42)|(v2_struct_0(X42)|~l1_orders_2(X42)|~m1_subset_1(X43,u1_struct_0(X42))|v2_struct_0(X44)|~l1_waybel_0(X44,X42)))&(l1_waybel_0(k3_waybel_2(X42,X43,X44),X42)|(v2_struct_0(X42)|~l1_orders_2(X42)|~m1_subset_1(X43,u1_struct_0(X42))|v2_struct_0(X44)|~l1_waybel_0(X44,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_waybel_2])])])])).
% 0.21/0.44  fof(c_0_10, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((~(v2_struct_0(k3_waybel_2(X1,X2,X3)))&v4_orders_2(k3_waybel_2(X1,X2,X3)))&v7_waybel_0(k3_waybel_2(X1,X2,X3)))&l1_waybel_0(k3_waybel_2(X1,X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t10_waybel_9])).
% 0.21/0.44  cnf(c_0_11, plain, (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))|v2_struct_0(X2)|v2_struct_0(X3)|X1!=k3_waybel_2(X3,X4,X2)|~v6_waybel_0(X1,X3)|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.44  cnf(c_0_12, plain, (l1_waybel_0(k3_waybel_2(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X3)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.44  cnf(c_0_13, plain, (v6_waybel_0(k3_waybel_2(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X3)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.44  fof(c_0_14, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_orders_2(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&((((~v2_struct_0(esk8_0)&v4_orders_2(esk8_0))&v7_waybel_0(esk8_0))&l1_waybel_0(esk8_0,esk6_0))&(v2_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~l1_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0),esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.21/0.44  fof(c_0_15, plain, ![X45, X46, X47]:((~v2_struct_0(k3_waybel_2(X45,X46,X47))|(v2_struct_0(X45)|~l1_orders_2(X45)|~m1_subset_1(X46,u1_struct_0(X45))|v2_struct_0(X47)|~l1_waybel_0(X47,X45)))&(v6_waybel_0(k3_waybel_2(X45,X46,X47),X45)|(v2_struct_0(X45)|~l1_orders_2(X45)|~m1_subset_1(X46,u1_struct_0(X45))|v2_struct_0(X47)|~l1_waybel_0(X47,X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_waybel_2])])])])).
% 0.21/0.44  fof(c_0_16, plain, ![X10, X11]:(~l1_struct_0(X10)|(~l1_waybel_0(X11,X10)|l1_orders_2(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.21/0.44  fof(c_0_17, plain, ![X9]:(~l1_orders_2(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.21/0.44  cnf(c_0_18, plain, (g1_orders_2(u1_struct_0(k3_waybel_2(X1,X2,X3)),u1_orders_2(k3_waybel_2(X1,X2,X3)))=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))|v2_struct_0(X1)|v2_struct_0(X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12]), c_0_13])).
% 0.21/0.44  cnf(c_0_19, negated_conjecture, (l1_waybel_0(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_23, plain, (v2_struct_0(X1)|v2_struct_0(X3)|~v2_struct_0(k3_waybel_2(X1,X2,X3))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.44  cnf(c_0_24, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  cnf(c_0_25, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  fof(c_0_26, plain, ![X30]:((~v4_orders_2(X30)|v4_orders_2(g1_orders_2(u1_struct_0(X30),u1_orders_2(X30)))|(v2_struct_0(X30)|~l1_orders_2(X30)))&(~v4_orders_2(g1_orders_2(u1_struct_0(X30),u1_orders_2(X30)))|v4_orders_2(X30)|(v2_struct_0(X30)|~l1_orders_2(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l16_yellow_6])])])])).
% 0.21/0.44  cnf(c_0_27, negated_conjecture, (g1_orders_2(u1_struct_0(k3_waybel_2(esk6_0,X1,esk8_0)),u1_orders_2(k3_waybel_2(esk6_0,X1,esk8_0)))=g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.21/0.44  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_29, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk6_0))|~v2_struct_0(k3_waybel_2(esk6_0,X1,esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.21/0.44  cnf(c_0_30, plain, (l1_orders_2(k3_waybel_2(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_waybel_0(X3,X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_12]), c_0_25])).
% 0.21/0.44  cnf(c_0_31, plain, (v4_orders_2(X1)|v2_struct_0(X1)|~v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.44  cnf(c_0_32, negated_conjecture, (g1_orders_2(u1_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0)),u1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0)))=g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.44  cnf(c_0_33, negated_conjecture, (~v2_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.21/0.44  cnf(c_0_34, negated_conjecture, (l1_orders_2(k3_waybel_2(esk6_0,X1,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_20])]), c_0_22]), c_0_21])).
% 0.21/0.44  cnf(c_0_35, negated_conjecture, (v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v4_orders_2(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)))|~l1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.21/0.44  cnf(c_0_36, negated_conjecture, (l1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.21/0.44  cnf(c_0_37, negated_conjecture, (l1_orders_2(esk8_0)|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.21/0.44  fof(c_0_38, plain, ![X29]:((~v7_waybel_0(X29)|v7_waybel_0(g1_orders_2(u1_struct_0(X29),u1_orders_2(X29)))|(v2_struct_0(X29)|~l1_orders_2(X29)))&(~v7_waybel_0(g1_orders_2(u1_struct_0(X29),u1_orders_2(X29)))|v7_waybel_0(X29)|(v2_struct_0(X29)|~l1_orders_2(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l15_yellow_6])])])])).
% 0.21/0.44  cnf(c_0_39, negated_conjecture, (v2_struct_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~l1_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_40, negated_conjecture, (v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v4_orders_2(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.21/0.44  cnf(c_0_41, plain, (v4_orders_2(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))|v2_struct_0(X1)|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.44  cnf(c_0_42, negated_conjecture, (v4_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_43, negated_conjecture, (l1_orders_2(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_20])])).
% 0.21/0.44  cnf(c_0_44, plain, (v7_waybel_0(X1)|v2_struct_0(X1)|~v7_waybel_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.44  cnf(c_0_45, negated_conjecture, (~v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_12]), c_0_28]), c_0_19]), c_0_20])]), c_0_33]), c_0_21]), c_0_22])).
% 0.21/0.44  cnf(c_0_46, negated_conjecture, (v4_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])]), c_0_21])).
% 0.21/0.44  cnf(c_0_47, negated_conjecture, (v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))|~v7_waybel_0(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)))|~l1_orders_2(k3_waybel_2(esk6_0,esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_33])).
% 0.21/0.44  cnf(c_0_48, negated_conjecture, (~v7_waybel_0(k3_waybel_2(esk6_0,esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.21/0.44  cnf(c_0_49, negated_conjecture, (~v7_waybel_0(g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_36])]), c_0_48])).
% 0.21/0.44  cnf(c_0_50, plain, (v7_waybel_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))|v2_struct_0(X1)|~v7_waybel_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.44  cnf(c_0_51, negated_conjecture, (v7_waybel_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_43])]), c_0_21]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 53
% 0.21/0.44  # Proof object clause steps            : 36
% 0.21/0.44  # Proof object formula steps           : 17
% 0.21/0.44  # Proof object conjectures             : 27
% 0.21/0.44  # Proof object clause conjectures      : 24
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 18
% 0.21/0.44  # Proof object initial formulas used   : 8
% 0.21/0.44  # Proof object generating inferences   : 14
% 0.21/0.44  # Proof object simplifying inferences  : 42
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 15
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 40
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 40
% 0.21/0.44  # Processed clauses                    : 398
% 0.21/0.44  # ...of these trivial                  : 0
% 0.21/0.44  # ...subsumed                          : 11
% 0.21/0.44  # ...remaining for further processing  : 387
% 0.21/0.44  # Other redundant clauses eliminated   : 7
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 92
% 0.21/0.44  # Backward-rewritten                   : 7
% 0.21/0.44  # Generated clauses                    : 1200
% 0.21/0.44  # ...of the previous two non-trivial   : 1193
% 0.21/0.44  # Contextual simplify-reflections      : 16
% 0.21/0.44  # Paramodulations                      : 1189
% 0.21/0.44  # Factorizations                       : 0
% 0.21/0.44  # Equation resolutions                 : 10
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 242
% 0.21/0.44  #    Positive orientable unit clauses  : 19
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 5
% 0.21/0.44  #    Non-unit-clauses                  : 218
% 0.21/0.44  # Current number of unprocessed clauses: 863
% 0.21/0.44  # ...number of literals in the above   : 3816
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 138
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 16053
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 5309
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 115
% 0.21/0.44  # Unit Clause-clause subsumption calls : 340
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 17
% 0.21/0.44  # BW rewrite match successes           : 3
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 43457
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.083 s
% 0.21/0.44  # System time              : 0.003 s
% 0.21/0.44  # Total time               : 0.086 s
% 0.21/0.44  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

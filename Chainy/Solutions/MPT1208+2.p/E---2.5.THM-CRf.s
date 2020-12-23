%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1208+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:03 EST 2020

% Result     : Theorem 28.54s
% Output     : CNFRefutation 28.54s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 239 expanded)
%              Number of clauses        :   32 (  84 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  249 (1153 expanded)
%              Number of equality atoms :   38 ( 146 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(d17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v14_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k6_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k1_lattices(X1,X2,X3) = X2
                    & k1_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

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

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v14_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t43_lattices])).

fof(c_0_10,plain,(
    ! [X68,X69,X70] :
      ( ( k1_lattices(X68,X69,X70) = X69
        | ~ m1_subset_1(X70,u1_struct_0(X68))
        | X69 != k6_lattices(X68)
        | ~ m1_subset_1(X69,u1_struct_0(X68))
        | ~ v14_lattices(X68)
        | v2_struct_0(X68)
        | ~ l2_lattices(X68) )
      & ( k1_lattices(X68,X70,X69) = X69
        | ~ m1_subset_1(X70,u1_struct_0(X68))
        | X69 != k6_lattices(X68)
        | ~ m1_subset_1(X69,u1_struct_0(X68))
        | ~ v14_lattices(X68)
        | v2_struct_0(X68)
        | ~ l2_lattices(X68) )
      & ( m1_subset_1(esk12_2(X68,X69),u1_struct_0(X68))
        | X69 = k6_lattices(X68)
        | ~ m1_subset_1(X69,u1_struct_0(X68))
        | ~ v14_lattices(X68)
        | v2_struct_0(X68)
        | ~ l2_lattices(X68) )
      & ( k1_lattices(X68,X69,esk12_2(X68,X69)) != X69
        | k1_lattices(X68,esk12_2(X68,X69),X69) != X69
        | X69 = k6_lattices(X68)
        | ~ m1_subset_1(X69,u1_struct_0(X68))
        | ~ v14_lattices(X68)
        | v2_struct_0(X68)
        | ~ l2_lattices(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).

fof(c_0_11,plain,(
    ! [X72] :
      ( v2_struct_0(X72)
      | ~ l2_lattices(X72)
      | m1_subset_1(k6_lattices(X72),u1_struct_0(X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

fof(c_0_12,plain,(
    ! [X232] :
      ( ( l1_lattices(X232)
        | ~ l3_lattices(X232) )
      & ( l2_lattices(X232)
        | ~ l3_lattices(X232) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v14_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & k4_lattices(esk1_0,k6_lattices(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_14,plain,(
    ! [X213] :
      ( ( ~ v2_struct_0(X213)
        | v2_struct_0(X213)
        | ~ v10_lattices(X213)
        | ~ l3_lattices(X213) )
      & ( v4_lattices(X213)
        | v2_struct_0(X213)
        | ~ v10_lattices(X213)
        | ~ l3_lattices(X213) )
      & ( v5_lattices(X213)
        | v2_struct_0(X213)
        | ~ v10_lattices(X213)
        | ~ l3_lattices(X213) )
      & ( v6_lattices(X213)
        | v2_struct_0(X213)
        | ~ v10_lattices(X213)
        | ~ l3_lattices(X213) )
      & ( v7_lattices(X213)
        | v2_struct_0(X213)
        | ~ v10_lattices(X213)
        | ~ l3_lattices(X213) )
      & ( v8_lattices(X213)
        | v2_struct_0(X213)
        | ~ v10_lattices(X213)
        | ~ l3_lattices(X213) )
      & ( v9_lattices(X213)
        | v2_struct_0(X213)
        | ~ v10_lattices(X213)
        | ~ l3_lattices(X213) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_15,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k6_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v6_lattices(X23)
      | ~ l1_lattices(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | k4_lattices(X23,X24,X25) = k4_lattices(X23,X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_20,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X292,X293,X294] :
      ( ( ~ r1_lattices(X292,X293,X294)
        | k1_lattices(X292,X293,X294) = X294
        | ~ m1_subset_1(X294,u1_struct_0(X292))
        | ~ m1_subset_1(X293,u1_struct_0(X292))
        | v2_struct_0(X292)
        | ~ l2_lattices(X292) )
      & ( k1_lattices(X292,X293,X294) != X294
        | r1_lattices(X292,X293,X294)
        | ~ m1_subset_1(X294,u1_struct_0(X292))
        | ~ m1_subset_1(X293,u1_struct_0(X292))
        | v2_struct_0(X292)
        | ~ l2_lattices(X292) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_25,plain,
    ( k1_lattices(X1,X2,k6_lattices(X1)) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v14_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( l1_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_22])]),c_0_23])).

fof(c_0_32,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v6_lattices(X29)
      | ~ l1_lattices(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | k4_lattices(X29,X30,X31) = k2_lattices(X29,X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_33,plain,(
    ! [X236,X237,X238] :
      ( ( ~ r1_lattices(X236,X237,X238)
        | k2_lattices(X236,X237,X238) = X237
        | ~ m1_subset_1(X238,u1_struct_0(X236))
        | ~ m1_subset_1(X237,u1_struct_0(X236))
        | v2_struct_0(X236)
        | ~ v8_lattices(X236)
        | ~ v9_lattices(X236)
        | ~ l3_lattices(X236) )
      & ( k2_lattices(X236,X237,X238) != X237
        | r1_lattices(X236,X237,X238)
        | ~ m1_subset_1(X238,u1_struct_0(X236))
        | ~ m1_subset_1(X237,u1_struct_0(X236))
        | v2_struct_0(X236)
        | ~ v8_lattices(X236)
        | ~ v9_lattices(X236)
        | ~ l3_lattices(X236) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_34,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) = k6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_28]),c_0_23])).

cnf(c_0_37,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( k4_lattices(esk1_0,X1,esk2_0) = k4_lattices(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_30]),c_0_31])]),c_0_23])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28]),c_0_36]),c_0_26])]),c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_22])]),c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_22])]),c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k4_lattices(esk1_0,k6_lattices(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( k4_lattices(esk1_0,k6_lattices(esk1_0),esk2_0) = k4_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k2_lattices(esk1_0,X1,k6_lattices(esk1_0)) = k4_lattices(esk1_0,X1,k6_lattices(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_30]),c_0_31])]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_18]),c_0_36]),c_0_26])]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_26]),c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------

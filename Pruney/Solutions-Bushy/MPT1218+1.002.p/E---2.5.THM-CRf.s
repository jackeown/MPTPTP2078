%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1218+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:56 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 506 expanded)
%              Number of clauses        :   68 ( 191 expanded)
%              Number of leaves         :   17 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          :  551 (2912 expanded)
%              Number of equality atoms :   23 ( 240 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v19_lattices(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r3_lattices(X1,X3,X4)
                        & r2_hidden(X3,X2) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d23_lattices)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t54_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v18_lattices(X2,X1)
            & v19_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => X2 = k2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_lattices)).

fof(d22_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v18_lattices(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r3_lattices(X1,X3,X4)
                        & r2_hidden(X4,X2) )
                     => r2_hidden(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattices)).

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(t23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_l1_lattices,axiom,(
    ! [X1] :
      ( l1_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(c_0_17,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ v19_lattices(X16,X15)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r3_lattices(X15,X17,X18)
        | ~ r2_hidden(X17,X16)
        | r2_hidden(X18,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk3_2(X15,X16),u1_struct_0(X15))
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk4_2(X15,X16),u1_struct_0(X15))
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( r3_lattices(X15,esk3_2(X15,X16),esk4_2(X15,X16))
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | v19_lattices(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d23_lattices])])])])])])).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | m1_subset_1(X52,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v18_lattices(X2,X1)
              & v19_lattices(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => X2 = k2_struct_0(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t54_lattices])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v18_lattices(X10,X9)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r3_lattices(X9,X11,X12)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X11,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_2(X9,X10),u1_struct_0(X9))
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk2_2(X9,X10),u1_struct_0(X9))
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( r3_lattices(X9,esk1_2(X9,X10),esk2_2(X9,X10))
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( r2_hidden(esk2_2(X9,X10),X10)
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | v18_lattices(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattices])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X4,X1)
    | v2_struct_0(X2)
    | ~ v19_lattices(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X3,X4)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v10_lattices(esk8_0)
    & l3_lattices(esk8_0)
    & ~ v1_xboole_0(esk9_0)
    & v18_lattices(esk9_0,esk8_0)
    & v19_lattices(esk9_0,esk8_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    & esk9_0 != k2_struct_0(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r3_lattices(X39,X40,X41)
        | r1_lattices(X39,X40,X41)
        | v2_struct_0(X39)
        | ~ v6_lattices(X39)
        | ~ v8_lattices(X39)
        | ~ v9_lattices(X39)
        | ~ l3_lattices(X39)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ m1_subset_1(X41,u1_struct_0(X39)) )
      & ( ~ r1_lattices(X39,X40,X41)
        | r3_lattices(X39,X40,X41)
        | v2_struct_0(X39)
        | ~ v6_lattices(X39)
        | ~ v8_lattices(X39)
        | ~ v9_lattices(X39)
        | ~ l3_lattices(X39)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ m1_subset_1(X41,u1_struct_0(X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_25,plain,(
    ! [X47,X48,X49] :
      ( v2_struct_0(X47)
      | ~ v6_lattices(X47)
      | ~ v8_lattices(X47)
      | ~ l3_lattices(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | ~ m1_subset_1(X49,u1_struct_0(X47))
      | r1_lattices(X47,k4_lattices(X47,X48,X49),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X1)
    | v2_struct_0(X2)
    | ~ v18_lattices(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X3,X4)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ v19_lattices(X2,X3)
    | ~ r2_hidden(X4,X2)
    | ~ r3_lattices(X3,X4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v19_lattices(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v10_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X4,X2)
    | ~ r3_lattices(X3,X1,X4)
    | ~ v18_lattices(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v18_lattices(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X60,X61,X62] :
      ( ( m1_subset_1(esk7_3(X60,X61,X62),X60)
        | X61 = X62
        | ~ m1_subset_1(X62,k1_zfmisc_1(X60))
        | ~ m1_subset_1(X61,k1_zfmisc_1(X60)) )
      & ( ~ r2_hidden(esk7_3(X60,X61,X62),X61)
        | ~ r2_hidden(esk7_3(X60,X61,X62),X62)
        | X61 = X62
        | ~ m1_subset_1(X62,k1_zfmisc_1(X60))
        | ~ m1_subset_1(X61,k1_zfmisc_1(X60)) )
      & ( r2_hidden(esk7_3(X60,X61,X62),X61)
        | r2_hidden(esk7_3(X60,X61,X62),X62)
        | X61 = X62
        | ~ m1_subset_1(X62,k1_zfmisc_1(X60))
        | ~ m1_subset_1(X61,k1_zfmisc_1(X60)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r3_lattices(esk8_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_39,plain,
    ( r3_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

fof(c_0_41,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v6_lattices(X6)
      | ~ l1_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k4_lattices(X6,X7,X8) = k4_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r3_lattices(esk8_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_36]),c_0_30]),c_0_31])]),c_0_32])).

fof(c_0_43,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v6_lattices(X26)
      | ~ l1_lattices(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | m1_subset_1(k4_lattices(X26,X27,X28),u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

fof(c_0_44,plain,(
    ! [X25] :
      ( ~ l1_struct_0(X25)
      | m1_subset_1(k2_struct_0(X25),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_hidden(esk7_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(k4_lattices(esk8_0,X1,X2),esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31])]),c_0_32]),c_0_40])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_lattices(esk8_0,X1,X2),esk9_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ m1_subset_1(k4_lattices(esk8_0,X1,X2),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_31])]),c_0_32]),c_0_40])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(esk7_3(u1_struct_0(esk8_0),X1,esk9_0),esk9_0)
    | r2_hidden(esk7_3(u1_struct_0(esk8_0),X1,esk9_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( esk9_0 != k2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(k4_lattices(esk8_0,X2,X1),esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_lattices(esk8_0,X1,X2),esk9_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_32]),c_0_40])).

fof(c_0_55,plain,(
    ! [X32] : m1_subset_1(esk5_1(X32),X32) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ r2_hidden(X1,k2_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_3(u1_struct_0(esk8_0),k2_struct_0(esk8_0),esk9_0),k2_struct_0(esk8_0))
    | r2_hidden(esk7_3(u1_struct_0(esk8_0),k2_struct_0(esk8_0),esk9_0),esk9_0)
    | ~ l1_struct_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_50]),c_0_52])).

fof(c_0_58,plain,(
    ! [X21] :
      ( ~ l1_struct_0(X21)
      | k2_struct_0(X21) = u1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_40])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_61,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X50,X51)
      | v1_xboole_0(X51)
      | r2_hidden(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_62,plain,(
    ! [X55,X56,X57] :
      ( ~ r2_hidden(X55,X56)
      | ~ m1_subset_1(X56,k1_zfmisc_1(X57))
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk7_3(u1_struct_0(esk8_0),k2_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40])).

cnf(c_0_64,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_65,plain,(
    ! [X29] :
      ( ~ l1_lattices(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_lattices])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk5_1(u1_struct_0(esk8_0)),esk9_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk7_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0))
    | ~ l1_struct_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( l1_struct_0(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk5_1(u1_struct_0(esk8_0)),esk9_0)
    | ~ m1_subset_1(X1,esk9_0)
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk8_0) != esk9_0
    | ~ l1_struct_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_64])).

fof(c_0_74,plain,(
    ! [X31] :
      ( ( l1_lattices(X31)
        | ~ l3_lattices(X31) )
      & ( l2_lattices(X31)
        | ~ l3_lattices(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_75,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk5_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk7_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),esk9_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_70]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_1(u1_struct_0(esk8_0)),esk9_0)
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_60])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk8_0) != esk9_0
    | ~ l1_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_71])).

cnf(c_0_79,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,esk5_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(u1_struct_0(esk8_0))) = esk9_0
    | r2_hidden(esk7_3(u1_struct_0(esk8_0),esk5_1(k1_zfmisc_1(u1_struct_0(esk8_0))),esk9_0),esk5_1(k1_zfmisc_1(u1_struct_0(esk8_0))))
    | r2_hidden(esk7_3(u1_struct_0(esk8_0),esk5_1(k1_zfmisc_1(u1_struct_0(esk8_0))),esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_60])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_28])).

cnf(c_0_83,plain,
    ( X2 = X3
    | ~ r2_hidden(esk7_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk7_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),esk9_0)
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(esk8_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_31])])).

cnf(c_0_86,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_60])).

cnf(c_0_87,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(u1_struct_0(esk8_0))) = esk9_0
    | ~ v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_81]),c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(esk7_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_28])]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( ~ m1_subset_1(esk7_3(u1_struct_0(esk8_0),u1_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_67]),c_0_89])).

cnf(c_0_91,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_92,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_28])]),c_0_85])).

cnf(c_0_93,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_64])).

fof(c_0_94,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_95,negated_conjecture,
    ( ~ l1_lattices(esk8_0)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_71])).

cnf(c_0_96,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( ~ l1_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_98,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( ~ l1_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_100,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( ~ l1_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_79]),c_0_31])]),
    [proof]).

%------------------------------------------------------------------------------

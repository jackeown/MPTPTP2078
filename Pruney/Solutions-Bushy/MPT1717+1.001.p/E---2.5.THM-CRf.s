%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1717+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  50 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :  162 ( 290 expanded)
%              Number of equality atoms :   15 (  36 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => k2_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t31_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ( ( m1_pre_topc(X2,X3)
                   => k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X3) )
                  & ( m1_pre_topc(X3,X2)
                   => k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) )
                  & ( k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                   => m1_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).

fof(t22_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( m1_pre_topc(X2,X3)
               => ( ~ r1_tsep_1(X2,X3)
                  & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => k2_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t26_tmap_1])).

fof(c_0_6,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X5,X4)
      | l1_pre_topc(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & k2_tsep_1(esk1_0,esk2_0,esk2_0) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X10,X11,X12] :
      ( ( ~ m1_pre_topc(X11,X12)
        | k2_tsep_1(X10,X11,X12) = g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))
        | r1_tsep_1(X11,X12)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( k2_tsep_1(X10,X11,X12) != g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))
        | m1_pre_topc(X11,X12)
        | r1_tsep_1(X11,X12)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ m1_pre_topc(X12,X11)
        | k2_tsep_1(X10,X11,X12) = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))
        | r1_tsep_1(X11,X12)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( k2_tsep_1(X10,X11,X12) != g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))
        | m1_pre_topc(X12,X11)
        | r1_tsep_1(X11,X12)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_tsep_1])])])])])).

fof(c_0_9,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r1_tsep_1(X7,X8)
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r1_tsep_1(X8,X7)
        | ~ m1_pre_topc(X7,X8)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_10,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tsep_1(X3,X2,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | r1_tsep_1(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | m1_pre_topc(X9,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( k2_tsep_1(X1,X2,X3) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k2_tsep_1(esk1_0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_11])]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( k2_tsep_1(esk1_0,esk2_0,esk2_0) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16])]),c_0_24]),c_0_25]),
    [proof]).

%------------------------------------------------------------------------------

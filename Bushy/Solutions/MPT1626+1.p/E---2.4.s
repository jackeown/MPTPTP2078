%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t6_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 153 expanded)
%              Number of clauses        :   22 (  46 expanded)
%              Number of leaves         :    3 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 (1540 expanded)
%              Number of equality atoms :   17 ( 216 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & v3_waybel_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( ( v2_waybel_0(X3,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
             => ( r2_yellow_0(X1,X3)
               => ( X3 = k1_xboole_0
                  | ( r2_yellow_0(X2,X3)
                    & k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t6_waybel_0.p',t6_waybel_0)).

fof(d3_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v3_waybel_0(X2,X1)
          <=> ! [X3] :
                ( ( v2_waybel_0(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
               => ( r2_yellow_0(X1,X3)
                 => ( X3 = k1_xboole_0
                    | r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t6_waybel_0.p',d3_waybel_0)).

fof(t64_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r2_yellow_0(X1,X3)
                  & r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r2_yellow_0(X2,X3)
                  & k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t6_waybel_0.p',t64_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v3_waybel_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( ( v2_waybel_0(X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
               => ( r2_yellow_0(X1,X3)
                 => ( X3 = k1_xboole_0
                    | ( r2_yellow_0(X2,X3)
                      & k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_waybel_0])).

fof(c_0_4,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v3_waybel_0(X12,X11)
        | ~ v2_waybel_0(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_yellow_0(X11,X13)
        | X13 = k1_xboole_0
        | r2_hidden(k2_yellow_0(X11,X13),u1_struct_0(X12))
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( v2_waybel_0(esk4_2(X11,X12),X12)
        | v3_waybel_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk4_2(X11,X12),k1_zfmisc_1(u1_struct_0(X12)))
        | v3_waybel_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_yellow_0(X11,esk4_2(X11,X12))
        | v3_waybel_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( esk4_2(X11,X12) != k1_xboole_0
        | v3_waybel_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r2_hidden(k2_yellow_0(X11,esk4_2(X11,X12)),u1_struct_0(X12))
        | v3_waybel_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_waybel_0])])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v4_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & v3_waybel_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & v2_waybel_0(esk3_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r2_yellow_0(esk1_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & ( ~ r2_yellow_0(esk2_0,esk3_0)
      | k2_yellow_0(esk2_0,esk3_0) != k2_yellow_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X40,X41,X42] :
      ( ( r2_yellow_0(X41,X42)
        | ~ r2_yellow_0(X40,X42)
        | ~ r2_hidden(k2_yellow_0(X40,X42),u1_struct_0(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v4_yellow_0(X41,X40)
        | ~ m1_yellow_0(X41,X40)
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ l1_orders_2(X40) )
      & ( k2_yellow_0(X41,X42) = k2_yellow_0(X40,X42)
        | ~ r2_yellow_0(X40,X42)
        | ~ r2_hidden(k2_yellow_0(X40,X42),u1_struct_0(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v4_yellow_0(X41,X40)
        | ~ m1_yellow_0(X41,X40)
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ l1_orders_2(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_yellow_0])])])])])).

cnf(c_0_7,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X2,X3),u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ v3_waybel_0(X1,X2)
    | ~ v2_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v2_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_yellow_0(X3,X2)
    | ~ r2_hidden(k2_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(k2_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,esk3_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ v3_waybel_0(esk2_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( v3_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk3_0)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))
    | ~ r2_yellow_0(X1,esk3_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ v4_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_yellow_0(X3,X2)
    | ~ r2_hidden(k2_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_yellow_0(esk2_0,esk3_0)
    | k2_yellow_0(esk2_0,esk3_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_20]),c_0_14]),c_0_21]),c_0_17]),c_0_22])]),c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk3_0) = k2_yellow_0(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))
    | ~ r2_yellow_0(X1,esk3_0)
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ v4_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_8]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk3_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_20]),c_0_15]),c_0_21]),c_0_17]),c_0_22])]),c_0_27]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------

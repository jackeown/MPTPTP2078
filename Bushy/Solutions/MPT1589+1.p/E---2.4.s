%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t68_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:47 EDT 2019

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   23 (  53 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  127 ( 487 expanded)
%              Number of equality atoms :    9 (  39 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2))
               => k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t68_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t64_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t17_yellow_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => ( r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2))
                 => k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_yellow_0])).

fof(c_0_4,plain,(
    ! [X34,X35,X36] :
      ( ( r2_yellow_0(X35,X36)
        | ~ r2_yellow_0(X34,X36)
        | ~ r2_hidden(k2_yellow_0(X34,X36),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | v2_struct_0(X35)
        | ~ v4_yellow_0(X35,X34)
        | ~ m1_yellow_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ l1_orders_2(X34) )
      & ( k2_yellow_0(X35,X36) = k2_yellow_0(X34,X36)
        | ~ r2_yellow_0(X34,X36)
        | ~ r2_hidden(k2_yellow_0(X34,X36),u1_struct_0(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | v2_struct_0(X35)
        | ~ v4_yellow_0(X35,X34)
        | ~ m1_yellow_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_yellow_0])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v3_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r2_hidden(k2_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0))
    & k2_yellow_0(esk2_0,esk3_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X20,X21] :
      ( ( r1_yellow_0(X20,X21)
        | v2_struct_0(X20)
        | ~ v5_orders_2(X20)
        | ~ v3_lattice3(X20)
        | ~ l1_orders_2(X20) )
      & ( r2_yellow_0(X20,X21)
        | v2_struct_0(X20)
        | ~ v5_orders_2(X20)
        | ~ v3_lattice3(X20)
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

cnf(c_0_10,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk3_0) = k2_yellow_0(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,esk3_0)
    | ~ r2_hidden(k2_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ v4_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_11,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk3_0) = k2_yellow_0(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_yellow_0(X1,esk3_0),u1_struct_0(esk2_0))
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ v4_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk1_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( k2_yellow_0(esk2_0,esk3_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------

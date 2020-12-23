%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t3_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:53 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  91 expanded)
%              Number of clauses        :   17 (  32 expanded)
%              Number of leaves         :    3 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 533 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fraenkel_a_2_0_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_0_yellow19(X2,X3))
      <=> ? [X4] :
            ( m1_connsp_2(X4,X2,X3)
            & X1 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',fraenkel_a_2_0_yellow19)).

fof(t3_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X3,k1_yellow19(X1,X2))
            <=> m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',t3_yellow19)).

fof(d1_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_yellow19(X1,X2) = a_2_0_yellow19(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t3_yellow19.p',d1_yellow19)).

fof(c_0_3,plain,(
    ! [X33,X34,X35,X37] :
      ( ( m1_connsp_2(esk9_3(X33,X34,X35),X34,X35)
        | ~ r2_hidden(X33,a_2_0_yellow19(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) )
      & ( X33 = esk9_3(X33,X34,X35)
        | ~ r2_hidden(X33,a_2_0_yellow19(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) )
      & ( ~ m1_connsp_2(X37,X34,X35)
        | X33 != X37
        | r2_hidden(X33,a_2_0_yellow19(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_yellow19])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( r2_hidden(X3,k1_yellow19(X1,X2))
              <=> m1_connsp_2(X3,X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow19])).

cnf(c_0_5,plain,
    ( r2_hidden(X4,a_2_0_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | X4 != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | k1_yellow19(X11,X12) = a_2_0_yellow19(X11,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_yellow19])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( ~ r2_hidden(esk3_0,k1_yellow19(esk1_0,esk2_0))
      | ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) )
    & ( r2_hidden(esk3_0,k1_yellow19(esk1_0,esk2_0))
      | m1_connsp_2(esk3_0,esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | k1_yellow19(X1,X2) = a_2_0_yellow19(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_connsp_2(esk9_3(X1,X2,X3),X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( X1 = esk9_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_yellow19(esk1_0,esk2_0))
    | ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k1_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,k1_yellow19(esk1_0,esk2_0))
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_21,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_yellow19(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,k1_yellow19(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14]),c_0_15]),c_0_16])]),c_0_20]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------

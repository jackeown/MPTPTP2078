%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow19__t11_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:49 EDT 2019

% Result     : Theorem 9.20s
% Output     : CNFRefutation 9.20s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 157 expanded)
%              Number of clauses        :   23 (  56 expanded)
%              Number of leaves         :    3 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  155 (1130 expanded)
%              Number of equality atoms :    8 (  44 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fraenkel_a_2_1_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X2) )
     => ( r2_hidden(X1,a_2_1_yellow19(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = X4
            & r1_waybel_0(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t11_yellow19.p',fraenkel_a_2_1_yellow19)).

fof(t11_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_hidden(X3,k2_yellow19(X1,X2))
            <=> ( r1_waybel_0(X1,X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t11_yellow19.p',t11_yellow19)).

fof(d3_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => k2_yellow19(X1,X2) = a_2_1_yellow19(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t11_yellow19.p',d3_yellow19)).

fof(c_0_3,plain,(
    ! [X29,X30,X31,X33] :
      ( ( m1_subset_1(esk8_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(X29,a_2_1_yellow19(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30) )
      & ( X29 = esk8_3(X29,X30,X31)
        | ~ r2_hidden(X29,a_2_1_yellow19(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30) )
      & ( r1_waybel_0(X30,X31,esk8_3(X29,X30,X31))
        | ~ r2_hidden(X29,a_2_1_yellow19(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))
        | X29 != X33
        | ~ r1_waybel_0(X30,X31,X33)
        | r2_hidden(X29,a_2_1_yellow19(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_yellow19])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( r2_hidden(X3,k2_yellow19(X1,X2))
              <=> ( r1_waybel_0(X1,X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_yellow19])).

cnf(c_0_5,plain,
    ( r2_hidden(X3,a_2_1_yellow19(X2,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X1
    | ~ r1_waybel_0(X2,X4,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ l1_struct_0(X11)
      | v2_struct_0(X12)
      | ~ l1_waybel_0(X12,X11)
      | k2_yellow19(X11,X12) = a_2_1_yellow19(X11,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_yellow19])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( X1 = esk8_3(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & ( ~ r2_hidden(esk3_0,k2_yellow19(esk1_0,esk2_0))
      | ~ r1_waybel_0(esk1_0,esk2_0,esk3_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( r1_waybel_0(esk1_0,esk2_0,esk3_0)
      | r2_hidden(esk3_0,k2_yellow19(esk1_0,esk2_0)) )
    & ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | r2_hidden(esk3_0,k2_yellow19(esk1_0,esk2_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_waybel_0(X2,X3,X1)
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_yellow19(X1,X2) = a_2_1_yellow19(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_yellow19(esk1_0,esk2_0))
    | ~ r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k2_yellow19(X2,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_waybel_0(X2,X3,X1)
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k2_yellow19(X2,X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(esk3_0,k2_yellow19(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r1_waybel_0(X1,X2,esk8_3(X3,X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,a_2_1_yellow19(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_2_1_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( r1_waybel_0(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk3_0,k2_yellow19(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_waybel_0(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_27,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,k2_yellow19(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_15]),c_0_16])]),c_0_26]),c_0_17]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------

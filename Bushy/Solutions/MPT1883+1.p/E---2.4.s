%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t51_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:53 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 ( 217 expanded)
%              Number of clauses        :   19 (  73 expanded)
%              Number of leaves         :    2 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 (1391 expanded)
%              Number of equality atoms :   13 ( 179 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v3_tex_2(X3,X1)
                <=> v4_tex_2(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t51_tex_2.p',t51_tex_2)).

fof(d8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v4_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t51_tex_2.p',d8_tex_2)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => ( v3_tex_2(X3,X1)
                  <=> v4_tex_2(X2,X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_tex_2])).

fof(c_0_3,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & esk3_0 = u1_struct_0(esk2_0)
    & ( ~ v3_tex_2(esk3_0,esk1_0)
      | ~ v4_tex_2(esk2_0,esk1_0) )
    & ( v3_tex_2(esk3_0,esk1_0)
      | v4_tex_2(esk2_0,esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).

fof(c_0_4,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v4_tex_2(X10,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | X11 != u1_struct_0(X10)
        | v3_tex_2(X11,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk4_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))
        | v4_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( esk4_2(X9,X10) = u1_struct_0(X10)
        | v4_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ v3_tex_2(esk4_2(X9,X10),X9)
        | v4_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

cnf(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X2)
    | v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( v3_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( esk4_2(esk1_0,X1) = u1_struct_0(X1)
    | v4_tex_2(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])])).

cnf(c_0_10,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,negated_conjecture,
    ( esk3_0 = u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,plain,
    ( v3_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ v3_tex_2(esk3_0,esk1_0)
    | ~ v4_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,negated_conjecture,
    ( esk4_2(esk1_0,esk2_0) = esk3_0
    | v4_tex_2(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v3_tex_2(esk3_0,X1)
    | v2_struct_0(X1)
    | ~ v4_tex_2(esk2_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_17,negated_conjecture,
    ( esk4_2(esk1_0,esk2_0) = esk3_0
    | ~ v3_tex_2(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(esk4_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( esk4_2(esk1_0,esk2_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_14]),c_0_16]),c_0_10]),c_0_7])]),c_0_5]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v3_tex_2(esk3_0,esk1_0)
    | v4_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_21,negated_conjecture,
    ( v4_tex_2(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10]),c_0_7])]),c_0_5]),c_0_20])).

cnf(c_0_22,negated_conjecture,
    ( ~ v3_tex_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_21])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_16]),c_0_10]),c_0_7])]),c_0_5]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------

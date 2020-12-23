%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t29_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:30 EDT 2019

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   35 (  99 expanded)
%              Number of clauses        :   22 (  40 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 331 expanded)
%              Number of equality atoms :    6 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t29_tex_2.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t29_tex_2.p',redefinition_k9_subset_1)).

fof(t28_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_tarski(X3,X2)
                  & v2_tex_2(X2,X1) )
               => v2_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t29_tex_2.p',t28_tex_2)).

fof(t29_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_tex_2(X2,X1)
                  | v2_tex_2(X3,X1) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t29_tex_2.p',t29_tex_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t29_tex_2.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t29_tex_2.p',commutativity_k3_xboole_0)).

fof(c_0_6,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(X60))
      | m1_subset_1(k9_subset_1(X60,X61,X62),k1_zfmisc_1(X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_7,plain,(
    ! [X105,X106,X107] :
      ( ~ m1_subset_1(X107,k1_zfmisc_1(X105))
      | k9_subset_1(X105,X106,X107) = k3_xboole_0(X106,X107) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_8,plain,(
    ! [X112,X113,X114] :
      ( ~ l1_pre_topc(X112)
      | ~ m1_subset_1(X113,k1_zfmisc_1(u1_struct_0(X112)))
      | ~ m1_subset_1(X114,k1_zfmisc_1(u1_struct_0(X112)))
      | ~ r1_tarski(X114,X113)
      | ~ v2_tex_2(X113,X112)
      | v2_tex_2(X114,X112) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v2_tex_2(X2,X1)
                    | v2_tex_2(X3,X1) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tex_2])).

cnf(c_0_12,plain,
    ( v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( v2_tex_2(esk2_0,esk1_0)
      | v2_tex_2(esk3_0,esk1_0) )
    & ~ v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X108,X109] : r1_tarski(k3_xboole_0(X108,X109),X108) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_16,plain,(
    ! [X55,X56] : k3_xboole_0(X55,X56) = k3_xboole_0(X56,X55) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_17,plain,
    ( v2_tex_2(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k3_xboole_0(X1,X2),X4)
    | ~ v2_tex_2(X4,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v2_tex_2(k3_xboole_0(X1,X2),esk1_0)
    | ~ r1_tarski(k3_xboole_0(X1,X2),esk3_0)
    | ~ v2_tex_2(esk3_0,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_tex_2(k3_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( v2_tex_2(k3_xboole_0(X1,esk3_0),esk1_0)
    | ~ v2_tex_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | v2_tex_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_tex_2(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( v2_tex_2(k3_xboole_0(X1,X2),esk1_0)
    | ~ r1_tarski(k3_xboole_0(X1,X2),esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_29]),c_0_19])]),c_0_30])])).

cnf(c_0_32,negated_conjecture,
    ( v2_tex_2(k3_xboole_0(X1,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( v2_tex_2(k3_xboole_0(esk2_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------

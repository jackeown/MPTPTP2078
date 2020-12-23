%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1871+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:56 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 481 expanded)
%              Number of clauses        :   37 ( 149 expanded)
%              Number of leaves         :    6 ( 116 expanded)
%              Depth                    :   11
%              Number of atoms          :  251 (4077 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & v4_pre_topc(X3,X1)
                  & v2_tex_2(X2,X1)
                  & v2_tex_2(X3,X1) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tex_2)).

fof(t31_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v4_pre_topc(X2,X1)
                    & v4_pre_topc(X3,X1) )
                 => ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
                    & v4_pre_topc(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v4_pre_topc(X2,X1)
                    & v4_pre_topc(X3,X1)
                    & v2_tex_2(X2,X1)
                    & v2_tex_2(X3,X1) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tex_2)).

fof(fc5_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v4_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v4_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(fc4_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v4_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v4_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v4_pre_topc(X2,X1)
                    & v4_pre_topc(X3,X1)
                    & v2_tex_2(X2,X1)
                    & v2_tex_2(X3,X1) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_tex_2])).

fof(c_0_7,plain,(
    ! [X16,X19,X20] :
      ( ( m1_subset_1(esk1_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X19,X16)
        | ~ v4_pre_topc(X20,X16)
        | ~ v2_tex_2(X19,X16)
        | ~ v2_tex_2(X20,X16)
        | v2_tex_2(k4_subset_1(u1_struct_0(X16),X19,X20),X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk2_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X19,X16)
        | ~ v4_pre_topc(X20,X16)
        | ~ v2_tex_2(X19,X16)
        | ~ v2_tex_2(X20,X16)
        | v2_tex_2(k4_subset_1(u1_struct_0(X16),X19,X20),X16)
        | ~ l1_pre_topc(X16) )
      & ( v4_pre_topc(esk1_1(X16),X16)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X19,X16)
        | ~ v4_pre_topc(X20,X16)
        | ~ v2_tex_2(X19,X16)
        | ~ v2_tex_2(X20,X16)
        | v2_tex_2(k4_subset_1(u1_struct_0(X16),X19,X20),X16)
        | ~ l1_pre_topc(X16) )
      & ( v4_pre_topc(esk2_1(X16),X16)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X19,X16)
        | ~ v4_pre_topc(X20,X16)
        | ~ v2_tex_2(X19,X16)
        | ~ v2_tex_2(X20,X16)
        | v2_tex_2(k4_subset_1(u1_struct_0(X16),X19,X20),X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X16),esk1_1(X16),esk2_1(X16)),X16)
        | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X16),esk1_1(X16),esk2_1(X16)),X16)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X19,X16)
        | ~ v4_pre_topc(X20,X16)
        | ~ v2_tex_2(X19,X16)
        | ~ v2_tex_2(X20,X16)
        | v2_tex_2(k4_subset_1(u1_struct_0(X16),X19,X20),X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tex_2])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v4_pre_topc(esk4_0,esk3_0)
    & v4_pre_topc(esk5_0,esk3_0)
    & v2_tex_2(esk4_0,esk3_0)
    & v2_tex_2(esk5_0,esk3_0)
    & ~ v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v2_tex_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v4_pre_topc(esk2_1(X1),X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v4_pre_topc(X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v4_pre_topc(X9,X7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
      | v4_pre_topc(k2_xboole_0(X8,X9),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_tops_1])])).

cnf(c_0_16,negated_conjecture,
    ( v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),X1,esk5_0),esk3_0)
    | m1_subset_1(esk2_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),X1,esk5_0),esk3_0)
    | v4_pre_topc(esk2_1(esk3_0),esk3_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( v4_pre_topc(esk1_1(X1),X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_24,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k4_subset_1(X10,X11,X12) = k2_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_25,plain,
    ( v4_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v4_pre_topc(esk2_1(esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),X1,esk5_0),esk3_0)
    | m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_30,negated_conjecture,
    ( v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),X1,esk5_0),esk3_0)
    | v4_pre_topc(esk1_1(esk3_0),esk3_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_10]),c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_31,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X4,X5,X6] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v4_pre_topc(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v4_pre_topc(X6,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | v4_pre_topc(k3_xboole_0(X5,X6),X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_tops_1])])).

cnf(c_0_33,negated_conjecture,
    ( v4_pre_topc(k2_xboole_0(X1,esk2_1(esk3_0)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_13]),c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( v4_pre_topc(esk1_1(esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(X1,esk2_1(esk3_0)) = k4_subset_1(u1_struct_0(esk3_0),X1,esk2_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

fof(c_0_37,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X15) = k3_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_38,plain,
    ( v4_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v4_pre_topc(k2_xboole_0(esk1_1(esk3_0),esk2_1(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(esk1_1(esk3_0),esk2_1(esk3_0)) = k4_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0),esk2_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_41,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( v4_pre_topc(k3_xboole_0(X1,esk2_1(esk3_0)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_13]),c_0_28])])).

cnf(c_0_43,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( v4_pre_topc(k4_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0),esk2_1(esk3_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),X1,esk2_1(esk3_0)) = k3_xboole_0(X1,esk2_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( v4_pre_topc(k3_xboole_0(esk1_1(esk3_0),esk2_1(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_35])])).

cnf(c_0_47,negated_conjecture,
    ( v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),X1,X2),esk3_0)
    | ~ v2_tex_2(X2,esk3_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X2,esk3_0)
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_13])])).

cnf(c_0_48,negated_conjecture,
    ( v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),X1,esk5_0),esk3_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v4_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_17]),c_0_18]),c_0_19])]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------

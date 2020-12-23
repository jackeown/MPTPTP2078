%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t39_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:32 EDT 2019

% Result     : Theorem 178.79s
% Output     : CNFRefutation 178.79s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 103 expanded)
%              Number of clauses        :   27 (  36 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :  251 (1156 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/tex_2__t39_tex_2.p',t39_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/tex_2__t39_tex_2.p',t31_tex_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t39_tex_2.p',redefinition_k9_subset_1)).

fof(fc5_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v4_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v4_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t39_tex_2.p',fc5_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t39_tex_2.p',redefinition_k4_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t39_tex_2.p',commutativity_k2_xboole_0)).

fof(fc4_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v4_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v4_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t39_tex_2.p',fc4_tops_1)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X232,X235,X236] :
      ( ( m1_subset_1(esk46_1(X232),k1_zfmisc_1(u1_struct_0(X232)))
        | ~ m1_subset_1(X235,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ m1_subset_1(X236,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ v4_pre_topc(X235,X232)
        | ~ v4_pre_topc(X236,X232)
        | ~ v2_tex_2(X235,X232)
        | ~ v2_tex_2(X236,X232)
        | v2_tex_2(k4_subset_1(u1_struct_0(X232),X235,X236),X232)
        | ~ l1_pre_topc(X232) )
      & ( m1_subset_1(esk47_1(X232),k1_zfmisc_1(u1_struct_0(X232)))
        | ~ m1_subset_1(X235,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ m1_subset_1(X236,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ v4_pre_topc(X235,X232)
        | ~ v4_pre_topc(X236,X232)
        | ~ v2_tex_2(X235,X232)
        | ~ v2_tex_2(X236,X232)
        | v2_tex_2(k4_subset_1(u1_struct_0(X232),X235,X236),X232)
        | ~ l1_pre_topc(X232) )
      & ( v4_pre_topc(esk46_1(X232),X232)
        | ~ m1_subset_1(X235,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ m1_subset_1(X236,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ v4_pre_topc(X235,X232)
        | ~ v4_pre_topc(X236,X232)
        | ~ v2_tex_2(X235,X232)
        | ~ v2_tex_2(X236,X232)
        | v2_tex_2(k4_subset_1(u1_struct_0(X232),X235,X236),X232)
        | ~ l1_pre_topc(X232) )
      & ( v4_pre_topc(esk47_1(X232),X232)
        | ~ m1_subset_1(X235,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ m1_subset_1(X236,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ v4_pre_topc(X235,X232)
        | ~ v4_pre_topc(X236,X232)
        | ~ v2_tex_2(X235,X232)
        | ~ v2_tex_2(X236,X232)
        | v2_tex_2(k4_subset_1(u1_struct_0(X232),X235,X236),X232)
        | ~ l1_pre_topc(X232) )
      & ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(X232),esk46_1(X232),esk47_1(X232)),X232)
        | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X232),esk46_1(X232),esk47_1(X232)),X232)
        | ~ m1_subset_1(X235,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ m1_subset_1(X236,k1_zfmisc_1(u1_struct_0(X232)))
        | ~ v4_pre_topc(X235,X232)
        | ~ v4_pre_topc(X236,X232)
        | ~ v2_tex_2(X235,X232)
        | ~ v2_tex_2(X236,X232)
        | v2_tex_2(k4_subset_1(u1_struct_0(X232),X235,X236),X232)
        | ~ l1_pre_topc(X232) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tex_2])])])])])).

fof(c_0_9,plain,(
    ! [X223,X224,X225] :
      ( ~ m1_subset_1(X225,k1_zfmisc_1(X223))
      | k9_subset_1(X223,X224,X225) = k3_xboole_0(X224,X225) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_10,plain,(
    ! [X135,X136,X137] :
      ( ~ v2_pre_topc(X135)
      | ~ l1_pre_topc(X135)
      | ~ v4_pre_topc(X136,X135)
      | ~ m1_subset_1(X136,k1_zfmisc_1(u1_struct_0(X135)))
      | ~ v4_pre_topc(X137,X135)
      | ~ m1_subset_1(X137,k1_zfmisc_1(u1_struct_0(X135)))
      | v4_pre_topc(k2_xboole_0(X136,X137),X135) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_tops_1])])).

fof(c_0_11,plain,(
    ! [X220,X221,X222] :
      ( ~ m1_subset_1(X221,k1_zfmisc_1(X220))
      | ~ m1_subset_1(X222,k1_zfmisc_1(X220))
      | k4_subset_1(X220,X221,X222) = k2_xboole_0(X221,X222) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_pre_topc(esk2_0,esk1_0)
    & v4_pre_topc(esk3_0,esk1_0)
    & v2_tex_2(esk2_0,esk1_0)
    & v2_tex_2(esk3_0,esk1_0)
    & ~ v2_tex_2(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_13,plain,(
    ! [X102,X103] : k2_xboole_0(X102,X103) = k2_xboole_0(X103,X102) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_14,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(X1),esk46_1(X1),esk47_1(X1)),X1)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),esk46_1(X1),esk47_1(X1)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk47_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( v4_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_tex_2(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v4_pre_topc(k4_subset_1(u1_struct_0(X1),esk46_1(X1),esk47_1(X1)),X1)
    | ~ v4_pre_topc(k3_xboole_0(esk46_1(X1),esk47_1(X1)),X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_24,plain,
    ( v4_pre_topc(k4_subset_1(X1,X2,X3),X4)
    | ~ v4_pre_topc(X3,X4)
    | ~ v4_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk46_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( v4_pre_topc(esk46_1(X1),X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( v4_pre_topc(esk47_1(X1),X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_28,plain,(
    ! [X130,X131,X132] :
      ( ~ v2_pre_topc(X130)
      | ~ l1_pre_topc(X130)
      | ~ v4_pre_topc(X131,X130)
      | ~ m1_subset_1(X131,k1_zfmisc_1(u1_struct_0(X130)))
      | ~ v4_pre_topc(X132,X130)
      | ~ m1_subset_1(X132,k1_zfmisc_1(u1_struct_0(X130)))
      | v4_pre_topc(k3_xboole_0(X131,X132),X130) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_tops_1])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_tex_2(k2_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_20]),c_0_21])])).

cnf(c_0_30,plain,
    ( k4_subset_1(X1,X2,X3) = k2_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_31,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_tex_2(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v4_pre_topc(k3_xboole_0(esk46_1(X1),esk47_1(X1)),X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_16]),c_0_26]),c_0_27])).

cnf(c_0_32,plain,
    ( v4_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_tex_2(k4_subset_1(X1,esk3_0,esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_tex_2(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25]),c_0_16]),c_0_26]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v2_tex_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21]),c_0_20]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t45_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:51 EDT 2019

% Result     : Theorem 156.51s
% Output     : CNFRefutation 156.51s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 823 expanded)
%              Number of clauses        :   45 ( 317 expanded)
%              Number of leaves         :    5 ( 188 expanded)
%              Depth                    :   13
%              Number of atoms          :  202 (4602 expanded)
%              Number of equality atoms :   46 (1187 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t45_tex_2.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t45_tex_2.p',dt_u1_pre_topc)).

fof(t45_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & X3 = X4
                      & v3_tex_2(X3,X1) )
                   => v3_tex_2(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t45_tex_2.p',t45_tex_2)).

fof(t25_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & X3 = X4
                      & v2_tex_2(X3,X1) )
                   => v2_tex_2(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t45_tex_2.p',t25_tex_2)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t45_tex_2.p',d7_tex_2)).

fof(c_0_5,plain,(
    ! [X98,X99,X100,X101] :
      ( ( X98 = X100
        | g1_pre_topc(X98,X99) != g1_pre_topc(X100,X101)
        | ~ m1_subset_1(X99,k1_zfmisc_1(k1_zfmisc_1(X98))) )
      & ( X99 = X101
        | g1_pre_topc(X98,X99) != g1_pre_topc(X100,X101)
        | ~ m1_subset_1(X99,k1_zfmisc_1(k1_zfmisc_1(X98))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_6,plain,(
    ! [X82] :
      ( ~ l1_pre_topc(X82)
      | m1_subset_1(u1_pre_topc(X82),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X82)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & X3 = X4
                        & v3_tex_2(X3,X1) )
                     => v3_tex_2(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_tex_2])).

cnf(c_0_8,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & esk3_0 = esk4_0
    & v3_tex_2(esk3_0,esk1_0)
    & ~ v3_tex_2(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X150,X151,X152,X153] :
      ( ~ l1_pre_topc(X150)
      | ~ l1_pre_topc(X151)
      | ~ m1_subset_1(X152,k1_zfmisc_1(u1_struct_0(X150)))
      | ~ m1_subset_1(X153,k1_zfmisc_1(u1_struct_0(X151)))
      | g1_pre_topc(u1_struct_0(X150),u1_pre_topc(X150)) != g1_pre_topc(u1_struct_0(X151),u1_pre_topc(X151))
      | X152 != X153
      | ~ v2_tex_2(X152,X150)
      | v2_tex_2(X153,X151) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_tex_2])])])).

cnf(c_0_12,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v2_tex_2(X4,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | X3 != X4
    | ~ v2_tex_2(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X75,X76,X77] :
      ( ( v2_tex_2(X76,X75)
        | ~ v3_tex_2(X76,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
        | ~ l1_pre_topc(X75) )
      & ( ~ m1_subset_1(X77,k1_zfmisc_1(u1_struct_0(X75)))
        | ~ v2_tex_2(X77,X75)
        | ~ r1_tarski(X76,X77)
        | X76 = X77
        | ~ v3_tex_2(X76,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
        | ~ l1_pre_topc(X75) )
      & ( m1_subset_1(esk5_2(X75,X76),k1_zfmisc_1(u1_struct_0(X75)))
        | ~ v2_tex_2(X76,X75)
        | v3_tex_2(X76,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
        | ~ l1_pre_topc(X75) )
      & ( v2_tex_2(esk5_2(X75,X76),X75)
        | ~ v2_tex_2(X76,X75)
        | v3_tex_2(X76,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
        | ~ l1_pre_topc(X75) )
      & ( r1_tarski(X76,esk5_2(X75,X76))
        | ~ v2_tex_2(X76,X75)
        | v3_tex_2(X76,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
        | ~ l1_pre_topc(X75) )
      & ( X76 != esk5_2(X75,X76)
        | ~ v2_tex_2(X76,X75)
        | v3_tex_2(X76,X75)
        | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
        | ~ l1_pre_topc(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v3_tex_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( u1_pre_topc(esk2_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,plain,
    ( v2_tex_2(X1,X2)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_tex_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v3_tex_2(esk4_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk1_0) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk5_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ v3_tex_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( v2_tex_2(esk4_0,esk2_0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))
    | ~ v2_tex_2(esk4_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_13]),c_0_14])])).

cnf(c_0_31,negated_conjecture,
    ( v2_tex_2(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_27]),c_0_14])])).

cnf(c_0_34,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,esk5_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_2(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_tex_2(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_14])]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v2_tex_2(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24]),c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_2(esk2_0,esk4_0))
    | ~ v2_tex_2(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_14])]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_2(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( v2_tex_2(esk5_2(X1,X2),X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk4_0
    | ~ r1_tarski(esk4_0,X1)
    | ~ v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_2(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_37])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_2(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v2_tex_2(esk5_2(esk2_0,esk4_0),esk2_0)
    | ~ v2_tex_2(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_14])]),c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( esk5_2(esk2_0,esk4_0) = esk4_0
    | ~ v2_tex_2(esk5_2(esk2_0,esk4_0),esk1_0)
    | ~ m1_subset_1(esk5_2(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( v2_tex_2(esk5_2(esk2_0,esk4_0),esk1_0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))
    | ~ v2_tex_2(esk5_2(esk2_0,esk4_0),X1)
    | ~ m1_subset_1(esk5_2(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_46]),c_0_26])])).

cnf(c_0_50,negated_conjecture,
    ( v2_tex_2(esk5_2(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_37])])).

cnf(c_0_51,negated_conjecture,
    ( esk5_2(esk2_0,esk4_0) = esk4_0
    | ~ v2_tex_2(esk5_2(esk2_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( v2_tex_2(esk5_2(esk2_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42]),c_0_27]),c_0_42]),c_0_46]),c_0_14])])).

cnf(c_0_53,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk5_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( esk5_2(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_37]),c_0_42]),c_0_24]),c_0_14])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------

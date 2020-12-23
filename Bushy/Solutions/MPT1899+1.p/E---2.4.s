%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t67_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:55 EDT 2019

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 929 expanded)
%              Number of clauses        :   41 ( 304 expanded)
%              Number of leaves         :    7 ( 230 expanded)
%              Depth                    :    9
%              Number of atoms          :  318 (7868 expanded)
%              Number of equality atoms :    9 (  67 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   35 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v1_tdlat_3(X2)
            & m1_pre_topc(X2,X1) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & m1_pre_topc(X2,X3)
              & v4_tex_2(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t67_tex_2.p',t67_tex_2)).

fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t67_tex_2.p',t26_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t67_tex_2.p',t1_tsep_1)).

fof(t65_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ~ ( r1_tarski(X2,X3)
                      & v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t67_tex_2.p',t65_tex_2)).

fof(t53_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v3_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & m1_pre_topc(X3,X1) )
                 => ~ ( v4_tex_2(X3,X1)
                      & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t67_tex_2.p',t53_tex_2)).

fof(t46_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t67_tex_2.p',t46_tex_2)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t67_tex_2.p',t4_tsep_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v1_tdlat_3(X2)
              & m1_pre_topc(X2,X1) )
           => ? [X3] :
                ( ~ v2_struct_0(X3)
                & v1_pre_topc(X3)
                & m1_pre_topc(X3,X1)
                & m1_pre_topc(X2,X3)
                & v4_tex_2(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_tex_2])).

fof(c_0_8,plain,(
    ! [X346,X347,X348] :
      ( ( ~ v2_tex_2(X348,X346)
        | v1_tdlat_3(X347)
        | X348 != u1_struct_0(X347)
        | ~ m1_subset_1(X348,k1_zfmisc_1(u1_struct_0(X346)))
        | v2_struct_0(X347)
        | ~ m1_pre_topc(X347,X346)
        | v2_struct_0(X346)
        | ~ l1_pre_topc(X346) )
      & ( ~ v1_tdlat_3(X347)
        | v2_tex_2(X348,X346)
        | X348 != u1_struct_0(X347)
        | ~ m1_subset_1(X348,k1_zfmisc_1(u1_struct_0(X346)))
        | v2_struct_0(X347)
        | ~ m1_pre_topc(X347,X346)
        | v2_struct_0(X346)
        | ~ l1_pre_topc(X346) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_9,plain,(
    ! [X344,X345] :
      ( ~ l1_pre_topc(X344)
      | ~ m1_pre_topc(X345,X344)
      | m1_subset_1(u1_struct_0(X345),k1_zfmisc_1(u1_struct_0(X344))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & v3_tdlat_3(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & v1_tdlat_3(esk2_0)
      & m1_pre_topc(esk2_0,esk1_0)
      & ( v2_struct_0(X7)
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,esk1_0)
        | ~ m1_pre_topc(esk2_0,X7)
        | ~ v4_tex_2(X7,esk1_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_11,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X367,X368] :
      ( ( m1_subset_1(esk86_2(X367,X368),k1_zfmisc_1(u1_struct_0(X367)))
        | ~ v2_tex_2(X368,X367)
        | ~ m1_subset_1(X368,k1_zfmisc_1(u1_struct_0(X367)))
        | v2_struct_0(X367)
        | ~ v2_pre_topc(X367)
        | ~ v3_tdlat_3(X367)
        | ~ l1_pre_topc(X367) )
      & ( r1_tarski(X368,esk86_2(X367,X368))
        | ~ v2_tex_2(X368,X367)
        | ~ m1_subset_1(X368,k1_zfmisc_1(u1_struct_0(X367)))
        | v2_struct_0(X367)
        | ~ v2_pre_topc(X367)
        | ~ v3_tdlat_3(X367)
        | ~ l1_pre_topc(X367) )
      & ( v3_tex_2(esk86_2(X367,X368),X367)
        | ~ v2_tex_2(X368,X367)
        | ~ m1_subset_1(X368,k1_zfmisc_1(u1_struct_0(X367)))
        | v2_struct_0(X367)
        | ~ v2_pre_topc(X367)
        | ~ v3_tdlat_3(X367)
        | ~ l1_pre_topc(X367) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X361,X362] :
      ( ( ~ v2_struct_0(esk85_2(X361,X362))
        | ~ v3_tex_2(X362,X361)
        | v1_xboole_0(X362)
        | ~ m1_subset_1(X362,k1_zfmisc_1(u1_struct_0(X361)))
        | v2_struct_0(X361)
        | ~ v2_pre_topc(X361)
        | ~ l1_pre_topc(X361) )
      & ( v1_pre_topc(esk85_2(X361,X362))
        | ~ v3_tex_2(X362,X361)
        | v1_xboole_0(X362)
        | ~ m1_subset_1(X362,k1_zfmisc_1(u1_struct_0(X361)))
        | v2_struct_0(X361)
        | ~ v2_pre_topc(X361)
        | ~ l1_pre_topc(X361) )
      & ( m1_pre_topc(esk85_2(X361,X362),X361)
        | ~ v3_tex_2(X362,X361)
        | v1_xboole_0(X362)
        | ~ m1_subset_1(X362,k1_zfmisc_1(u1_struct_0(X361)))
        | v2_struct_0(X361)
        | ~ v2_pre_topc(X361)
        | ~ l1_pre_topc(X361) )
      & ( v4_tex_2(esk85_2(X361,X362),X361)
        | ~ v3_tex_2(X362,X361)
        | v1_xboole_0(X362)
        | ~ m1_subset_1(X362,k1_zfmisc_1(u1_struct_0(X361)))
        | v2_struct_0(X361)
        | ~ v2_pre_topc(X361)
        | ~ l1_pre_topc(X361) )
      & ( X362 = u1_struct_0(esk85_2(X361,X362))
        | ~ v3_tex_2(X362,X361)
        | v1_xboole_0(X362)
        | ~ m1_subset_1(X362,k1_zfmisc_1(u1_struct_0(X361)))
        | v2_struct_0(X361)
        | ~ v2_pre_topc(X361)
        | ~ l1_pre_topc(X361) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t53_tex_2])])])])])])).

fof(c_0_17,plain,(
    ! [X353,X354] :
      ( v2_struct_0(X353)
      | ~ v2_pre_topc(X353)
      | ~ l1_pre_topc(X353)
      | ~ v1_xboole_0(X354)
      | ~ m1_subset_1(X354,k1_zfmisc_1(u1_struct_0(X353)))
      | ~ v3_tex_2(X354,X353) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

cnf(c_0_18,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( v3_tex_2(esk86_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_14]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( v3_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( m1_pre_topc(esk85_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk86_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_19]),c_0_15])]),c_0_20]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v3_tex_2(esk86_2(esk1_0,u1_struct_0(esk2_0)),esk1_0)
    | ~ v2_tex_2(u1_struct_0(esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15]),c_0_24]),c_0_25])]),c_0_21])).

cnf(c_0_31,plain,
    ( X1 = u1_struct_0(esk85_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( v1_pre_topc(esk85_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk85_2(X1,X2))
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( v4_tex_2(esk85_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
    ! [X358,X359,X360] :
      ( ( ~ r1_tarski(u1_struct_0(X359),u1_struct_0(X360))
        | m1_pre_topc(X359,X360)
        | ~ m1_pre_topc(X360,X358)
        | ~ m1_pre_topc(X359,X358)
        | ~ v2_pre_topc(X358)
        | ~ l1_pre_topc(X358) )
      & ( ~ m1_pre_topc(X359,X360)
        | r1_tarski(u1_struct_0(X359),u1_struct_0(X360))
        | ~ m1_pre_topc(X360,X358)
        | ~ m1_pre_topc(X359,X358)
        | ~ v2_pre_topc(X358)
        | ~ l1_pre_topc(X358) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_36,plain,
    ( m1_pre_topc(esk85_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk86_2(esk1_0,u1_struct_0(esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_15]),c_0_24]),c_0_25])]),c_0_21]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( v3_tex_2(esk86_2(esk1_0,u1_struct_0(esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29])])).

cnf(c_0_39,plain,
    ( u1_struct_0(esk85_2(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,esk86_2(X2,X1))
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v3_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( v1_pre_topc(esk85_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk85_2(X1,X2)) ),
    inference(csr,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_43,plain,
    ( v4_tex_2(esk85_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_44,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk85_2(esk1_0,esk86_2(esk1_0,u1_struct_0(esk2_0))),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_15]),c_0_25])]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk85_2(esk1_0,esk86_2(esk1_0,u1_struct_0(esk2_0)))) = esk86_2(esk1_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_38]),c_0_15]),c_0_25])]),c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),esk86_2(esk1_0,u1_struct_0(esk2_0)))
    | ~ v2_tex_2(u1_struct_0(esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_15]),c_0_24]),c_0_25])]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ v4_tex_2(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( v1_pre_topc(esk85_2(esk1_0,esk86_2(esk1_0,u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_38]),c_0_15]),c_0_25])]),c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk85_2(esk1_0,esk86_2(esk1_0,u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_37]),c_0_38]),c_0_15]),c_0_25])]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( v4_tex_2(esk85_2(esk1_0,esk86_2(esk1_0,u1_struct_0(esk2_0))),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_38]),c_0_15]),c_0_25])]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(X1,esk85_2(esk1_0,esk86_2(esk1_0,u1_struct_0(esk2_0))))
    | ~ r1_tarski(u1_struct_0(X1),esk86_2(esk1_0,u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_15]),c_0_25])]),c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),esk86_2(esk1_0,u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_29])])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_pre_topc(esk2_0,esk85_2(esk1_0,esk86_2(esk1_0,u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_45]),c_0_49])]),c_0_50]),c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_14]),c_0_53])]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1883+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 16.75s
% Output     : CNFRefutation 16.75s
% Verified   : 
% Statistics : Number of formulae       :   23 ( 111 expanded)
%              Number of clauses        :   16 (  36 expanded)
%              Number of leaves         :    3 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 705 expanded)
%              Number of equality atoms :   10 (  86 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT028+2.ax',t1_tsep_1)).

fof(c_0_3,negated_conjecture,(
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

fof(c_0_4,plain,(
    ! [X11705,X11706,X11707] :
      ( ( ~ v4_tex_2(X11706,X11705)
        | ~ m1_subset_1(X11707,k1_zfmisc_1(u1_struct_0(X11705)))
        | X11707 != u1_struct_0(X11706)
        | v3_tex_2(X11707,X11705)
        | ~ m1_pre_topc(X11706,X11705)
        | v2_struct_0(X11705)
        | ~ l1_pre_topc(X11705) )
      & ( m1_subset_1(esk1310_2(X11705,X11706),k1_zfmisc_1(u1_struct_0(X11705)))
        | v4_tex_2(X11706,X11705)
        | ~ m1_pre_topc(X11706,X11705)
        | v2_struct_0(X11705)
        | ~ l1_pre_topc(X11705) )
      & ( esk1310_2(X11705,X11706) = u1_struct_0(X11706)
        | v4_tex_2(X11706,X11705)
        | ~ m1_pre_topc(X11706,X11705)
        | v2_struct_0(X11705)
        | ~ l1_pre_topc(X11705) )
      & ( ~ v3_tex_2(esk1310_2(X11705,X11706),X11705)
        | v4_tex_2(X11706,X11705)
        | ~ m1_pre_topc(X11706,X11705)
        | v2_struct_0(X11705)
        | ~ l1_pre_topc(X11705) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1364_0)
    & l1_pre_topc(esk1364_0)
    & m1_pre_topc(esk1365_0,esk1364_0)
    & m1_subset_1(esk1366_0,k1_zfmisc_1(u1_struct_0(esk1364_0)))
    & esk1366_0 = u1_struct_0(esk1365_0)
    & ( ~ v3_tex_2(esk1366_0,esk1364_0)
      | ~ v4_tex_2(esk1365_0,esk1364_0) )
    & ( v3_tex_2(esk1366_0,esk1364_0)
      | v4_tex_2(esk1365_0,esk1364_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(esk1310_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_pre_topc(esk1365_0,esk1364_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1364_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1364_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( esk1310_2(X1,X2) = u1_struct_0(X2)
    | v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( esk1366_0 = u1_struct_0(esk1365_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,plain,(
    ! [X11076,X11077] :
      ( ~ l1_pre_topc(X11076)
      | ~ m1_pre_topc(X11077,X11076)
      | m1_subset_1(u1_struct_0(X11077),k1_zfmisc_1(u1_struct_0(X11076))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_13,negated_conjecture,
    ( v4_tex_2(esk1365_0,esk1364_0)
    | ~ v3_tex_2(esk1310_2(esk1364_0,esk1365_0),esk1364_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])]),c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( esk1310_2(esk1364_0,esk1365_0) = esk1366_0
    | v4_tex_2(esk1365_0,esk1364_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_7]),c_0_11]),c_0_8])]),c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v3_tex_2(esk1366_0,esk1364_0)
    | v4_tex_2(esk1365_0,esk1364_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( v3_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v3_tex_2(esk1366_0,esk1364_0)
    | ~ v4_tex_2(esk1365_0,esk1364_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( v4_tex_2(esk1365_0,esk1364_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( v3_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | ~ v4_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v3_tex_2(esk1366_0,esk1364_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_7]),c_0_11]),c_0_19]),c_0_8])]),c_0_21]),c_0_9]),
    [proof]).
%------------------------------------------------------------------------------

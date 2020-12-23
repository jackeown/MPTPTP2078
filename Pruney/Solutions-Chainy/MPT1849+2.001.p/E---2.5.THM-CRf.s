%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:21 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  113 (1012 expanded)
%              Number of clauses        :   74 ( 378 expanded)
%              Number of leaves         :   19 ( 255 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 (4043 expanded)
%              Number of equality atoms :   71 ( 695 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_tex_2(X2,X1)
            & m1_pre_topc(X2,X1) )
         => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_tex_2(X2,X1)
              & m1_pre_topc(X2,X1) )
           => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tex_2])).

fof(c_0_20,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v1_tex_2(X34,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | X35 != u1_struct_0(X34)
        | v1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk1_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))
        | v1_tex_2(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( esk1_2(X33,X34) = u1_struct_0(X34)
        | v1_tex_2(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ v1_subset_1(esk1_2(X33,X34),u1_struct_0(X33))
        | v1_tex_2(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v1_tex_2(esk3_0,esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_22,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X37,X38] :
      ( ( ~ v1_subset_1(X38,X37)
        | X38 != X37
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) )
      & ( X38 = X37
        | v1_subset_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( esk1_2(esk2_0,esk3_0) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_29,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | r1_tarski(u1_struct_0(X32),u1_struct_0(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_28]),c_0_24])]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_23]),c_0_24])]),c_0_25])).

fof(c_0_35,plain,(
    ! [X14,X15] :
      ( ( v1_pre_topc(g1_pre_topc(X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) )
      & ( l1_pre_topc(g1_pre_topc(X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_36,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | m1_subset_1(u1_pre_topc(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_37,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X20 = X22
        | g1_pre_topc(X20,X21) != g1_pre_topc(X22,X23)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))) )
      & ( X21 = X23
        | g1_pre_topc(X20,X21) != g1_pre_topc(X22,X23)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_41,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)))
      | m1_pre_topc(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_42,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | m1_pre_topc(X30,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_43,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | ~ v1_pre_topc(X9)
      | X9 = g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_47,plain,(
    ! [X28,X29] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)),X28)
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_48,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_53,plain,(
    ! [X26,X27] :
      ( ( ~ m1_pre_topc(X26,X27)
        | m1_pre_topc(X26,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_pre_topc(X26,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
        | m1_pre_topc(X26,X27)
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_54,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | l1_pre_topc(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_55,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_56,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_24])])).

cnf(c_0_59,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_pre_topc(X1)
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56])]),c_0_52])).

cnf(c_0_63,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0)
    | ~ m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_24])])).

cnf(c_0_65,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_66,plain,(
    ! [X10,X11,X12] :
      ( ( X12 != k1_pre_topc(X10,X11)
        | k2_struct_0(X12) = X11
        | ~ v1_pre_topc(X12)
        | ~ m1_pre_topc(X12,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( k2_struct_0(X12) != X11
        | X12 = k1_pre_topc(X10,X11)
        | ~ v1_pre_topc(X12)
        | ~ m1_pre_topc(X12,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_67,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k2_struct_0(X13) = u1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_68,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_69,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_70,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_23]),c_0_24])])).

cnf(c_0_72,plain,
    ( X1 = k1_pre_topc(X3,X2)
    | k2_struct_0(X1) != X2
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_76,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_40])).

cnf(c_0_78,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))) = u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( k1_pre_topc(X1,k2_struct_0(X2)) = X2
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_71])).

fof(c_0_83,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_84,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_85,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_23]),c_0_24])])).

cnf(c_0_86,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_23]),c_0_24])])).

cnf(c_0_87,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_23]),c_0_24])])).

cnf(c_0_88,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),X1)
    | ~ m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_77]),c_0_52])).

cnf(c_0_89,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_pre_topc(esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_70]),c_0_24])])).

cnf(c_0_90,plain,
    ( k1_pre_topc(X1,u1_struct_0(X2)) = X2
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_61])).

cnf(c_0_91,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_56])]),c_0_52]),c_0_63])).

cnf(c_0_92,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))),esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_82]),c_0_24])])).

cnf(c_0_93,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_40]),c_0_85])])).

cnf(c_0_96,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_86,c_0_40])).

cnf(c_0_97,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_87,c_0_40])).

cnf(c_0_98,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_99,plain,
    ( k1_pre_topc(X1,u1_struct_0(X2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_63])).

cnf(c_0_100,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_70]),c_0_24])])).

cnf(c_0_101,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_56])]),c_0_96]),c_0_97])])).

cnf(c_0_103,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),esk2_0)
    | ~ m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_98]),c_0_24])])).

cnf(c_0_104,negated_conjecture,
    ( k1_pre_topc(esk2_0,u1_struct_0(esk2_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_24]),c_0_101])])).

cnf(c_0_105,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_106,negated_conjecture,
    ( k1_pre_topc(X1,u1_struct_0(esk2_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_102]),c_0_96])])).

cnf(c_0_107,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),esk2_0)
    | ~ m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_91]),c_0_24])])).

cnf(c_0_108,negated_conjecture,
    ( k1_pre_topc(esk2_0,u1_struct_0(esk2_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_52]),c_0_24])])).

cnf(c_0_109,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)) != g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_105,c_0_40])).

cnf(c_0_110,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108]),c_0_24]),c_0_101])]),c_0_109])).

cnf(c_0_111,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_65]),c_0_23]),c_0_24])])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_52]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:50:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.88/1.03  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.88/1.03  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.88/1.03  #
% 0.88/1.03  # Preprocessing time       : 0.029 s
% 0.88/1.03  # Presaturation interreduction done
% 0.88/1.03  
% 0.88/1.03  # Proof found!
% 0.88/1.03  # SZS status Theorem
% 0.88/1.03  # SZS output start CNFRefutation
% 0.88/1.03  fof(t16_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tex_2)).
% 0.88/1.03  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.88/1.03  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.88/1.03  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.88/1.03  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.88/1.03  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.88/1.03  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.88/1.03  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.88/1.03  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.88/1.03  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.88/1.03  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.88/1.03  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.88/1.03  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.88/1.03  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.88/1.03  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.88/1.03  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.88/1.03  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.88/1.03  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.88/1.03  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.88/1.03  fof(c_0_19, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_tex_2(X2,X1))&m1_pre_topc(X2,X1))=>g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), inference(assume_negation,[status(cth)],[t16_tex_2])).
% 0.88/1.03  fof(c_0_20, plain, ![X33, X34, X35]:((~v1_tex_2(X34,X33)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|(X35!=u1_struct_0(X34)|v1_subset_1(X35,u1_struct_0(X33))))|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&((m1_subset_1(esk1_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))|v1_tex_2(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&((esk1_2(X33,X34)=u1_struct_0(X34)|v1_tex_2(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&(~v1_subset_1(esk1_2(X33,X34),u1_struct_0(X33))|v1_tex_2(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.88/1.03  fof(c_0_21, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&((~v1_tex_2(esk3_0,esk2_0)&m1_pre_topc(esk3_0,esk2_0))&g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.88/1.03  cnf(c_0_22, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.88/1.03  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.88/1.03  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.88/1.03  cnf(c_0_25, negated_conjecture, (~v1_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.88/1.03  fof(c_0_26, plain, ![X37, X38]:((~v1_subset_1(X38,X37)|X38!=X37|~m1_subset_1(X38,k1_zfmisc_1(X37)))&(X38=X37|v1_subset_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.88/1.03  cnf(c_0_27, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.88/1.03  cnf(c_0_28, negated_conjecture, (esk1_2(esk2_0,esk3_0)=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25])).
% 0.88/1.03  cnf(c_0_29, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.88/1.03  fof(c_0_30, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.88/1.03  fof(c_0_31, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|r1_tarski(u1_struct_0(X32),u1_struct_0(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.88/1.03  cnf(c_0_32, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.88/1.03  cnf(c_0_33, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_23]), c_0_28]), c_0_24])]), c_0_25])).
% 0.88/1.03  cnf(c_0_34, negated_conjecture, (~v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_23]), c_0_24])]), c_0_25])).
% 0.88/1.03  fof(c_0_35, plain, ![X14, X15]:((v1_pre_topc(g1_pre_topc(X14,X15))|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))&(l1_pre_topc(g1_pre_topc(X14,X15))|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.88/1.03  fof(c_0_36, plain, ![X19]:(~l1_pre_topc(X19)|m1_subset_1(u1_pre_topc(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.88/1.03  fof(c_0_37, plain, ![X20, X21, X22, X23]:((X20=X22|g1_pre_topc(X20,X21)!=g1_pre_topc(X22,X23)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))))&(X21=X23|g1_pre_topc(X20,X21)!=g1_pre_topc(X22,X23)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.88/1.03  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.88/1.03  cnf(c_0_39, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.88/1.03  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.88/1.03  fof(c_0_41, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)))|m1_pre_topc(X25,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.88/1.03  fof(c_0_42, plain, ![X30]:(~l1_pre_topc(X30)|m1_pre_topc(X30,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.88/1.03  cnf(c_0_43, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.88/1.03  cnf(c_0_44, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.88/1.03  cnf(c_0_45, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.88/1.03  fof(c_0_46, plain, ![X9]:(~l1_pre_topc(X9)|(~v1_pre_topc(X9)|X9=g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.88/1.03  fof(c_0_47, plain, ![X28, X29]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|~m1_pre_topc(X29,X28)|~l1_pre_topc(X28))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)),X28)|~m1_pre_topc(X29,X28)|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.88/1.03  cnf(c_0_48, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.88/1.03  cnf(c_0_49, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(X1))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.88/1.03  cnf(c_0_50, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.88/1.03  cnf(c_0_51, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.88/1.03  cnf(c_0_52, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.88/1.03  fof(c_0_53, plain, ![X26, X27]:((~m1_pre_topc(X26,X27)|m1_pre_topc(X26,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|~l1_pre_topc(X27)|~l1_pre_topc(X26))&(~m1_pre_topc(X26,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|m1_pre_topc(X26,X27)|~l1_pre_topc(X27)|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.88/1.03  fof(c_0_54, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|l1_pre_topc(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.88/1.03  cnf(c_0_55, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.88/1.03  cnf(c_0_56, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.88/1.03  cnf(c_0_57, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.88/1.03  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_24])])).
% 0.88/1.03  cnf(c_0_59, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.88/1.03  cnf(c_0_60, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.88/1.03  cnf(c_0_61, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.88/1.03  cnf(c_0_62, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_pre_topc(X1)|~v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56])]), c_0_52])).
% 0.88/1.03  cnf(c_0_63, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_57, c_0_51])).
% 0.88/1.03  cnf(c_0_64, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)|~m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_24])])).
% 0.88/1.03  cnf(c_0_65, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_60, c_0_61])).
% 0.88/1.03  fof(c_0_66, plain, ![X10, X11, X12]:((X12!=k1_pre_topc(X10,X11)|k2_struct_0(X12)=X11|(~v1_pre_topc(X12)|~m1_pre_topc(X12,X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(k2_struct_0(X12)!=X11|X12=k1_pre_topc(X10,X11)|(~v1_pre_topc(X12)|~m1_pre_topc(X12,X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.88/1.03  fof(c_0_67, plain, ![X13]:(~l1_struct_0(X13)|k2_struct_0(X13)=u1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.88/1.03  fof(c_0_68, plain, ![X16]:(~l1_pre_topc(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.88/1.03  cnf(c_0_69, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.88/1.03  cnf(c_0_70, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.88/1.03  cnf(c_0_71, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_23]), c_0_24])])).
% 0.88/1.03  cnf(c_0_72, plain, (X1=k1_pre_topc(X3,X2)|k2_struct_0(X1)!=X2|~v1_pre_topc(X1)|~m1_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.88/1.03  cnf(c_0_73, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.88/1.03  cnf(c_0_74, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.88/1.03  cnf(c_0_75, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.88/1.03  cnf(c_0_76, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_61, c_0_69])).
% 0.88/1.03  cnf(c_0_77, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_69, c_0_40])).
% 0.88/1.03  cnf(c_0_78, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))=u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.88/1.03  cnf(c_0_79, plain, (k1_pre_topc(X1,k2_struct_0(X2))=X2|~m1_pre_topc(X2,X1)|~v1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_72])).
% 0.88/1.03  cnf(c_0_80, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.88/1.03  cnf(c_0_81, plain, (u1_struct_0(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_75, c_0_44])).
% 0.88/1.03  cnf(c_0_82, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_59, c_0_71])).
% 0.88/1.03  fof(c_0_83, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.88/1.03  fof(c_0_84, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.88/1.03  cnf(c_0_85, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_23]), c_0_24])])).
% 0.88/1.03  cnf(c_0_86, negated_conjecture, (v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_23]), c_0_24])])).
% 0.88/1.03  cnf(c_0_87, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_23]), c_0_24])])).
% 0.88/1.03  cnf(c_0_88, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),X1)|~m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_77]), c_0_52])).
% 0.88/1.03  cnf(c_0_89, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_pre_topc(esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_70]), c_0_24])])).
% 0.88/1.03  cnf(c_0_90, plain, (k1_pre_topc(X1,u1_struct_0(X2))=X2|~m1_pre_topc(X2,X1)|~v1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_61])).
% 0.88/1.03  cnf(c_0_91, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_56])]), c_0_52]), c_0_63])).
% 0.88/1.03  cnf(c_0_92, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))),esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_82]), c_0_24])])).
% 0.88/1.03  cnf(c_0_93, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.88/1.03  cnf(c_0_94, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.88/1.03  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk2_0)=X1|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))!=g1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_40]), c_0_85])])).
% 0.88/1.03  cnf(c_0_96, negated_conjecture, (v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)))), inference(rw,[status(thm)],[c_0_86, c_0_40])).
% 0.88/1.03  cnf(c_0_97, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)))), inference(rw,[status(thm)],[c_0_87, c_0_40])).
% 0.88/1.03  cnf(c_0_98, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.88/1.03  cnf(c_0_99, plain, (k1_pre_topc(X1,u1_struct_0(X2))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_63])).
% 0.88/1.03  cnf(c_0_100, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_70]), c_0_24])])).
% 0.88/1.03  cnf(c_0_101, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_93, c_0_94])).
% 0.88/1.03  cnf(c_0_102, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_56])]), c_0_96]), c_0_97])])).
% 0.88/1.03  cnf(c_0_103, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),esk2_0)|~m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_98]), c_0_24])])).
% 0.88/1.03  cnf(c_0_104, negated_conjecture, (k1_pre_topc(esk2_0,u1_struct_0(esk2_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_24]), c_0_101])])).
% 0.88/1.03  cnf(c_0_105, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.88/1.03  cnf(c_0_106, negated_conjecture, (k1_pre_topc(X1,u1_struct_0(esk2_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))|~m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_102]), c_0_96])])).
% 0.88/1.03  cnf(c_0_107, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0)),esk2_0)|~m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_91]), c_0_24])])).
% 0.88/1.03  cnf(c_0_108, negated_conjecture, (k1_pre_topc(esk2_0,u1_struct_0(esk2_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_52]), c_0_24])])).
% 0.88/1.03  cnf(c_0_109, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk3_0))!=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(rw,[status(thm)],[c_0_105, c_0_40])).
% 0.88/1.03  cnf(c_0_110, negated_conjecture, (~m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108]), c_0_24]), c_0_101])]), c_0_109])).
% 0.88/1.03  cnf(c_0_111, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_65]), c_0_23]), c_0_24])])).
% 0.88/1.03  cnf(c_0_112, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_52]), c_0_24])]), ['proof']).
% 0.88/1.03  # SZS output end CNFRefutation
% 0.88/1.03  # Proof object total steps             : 113
% 0.88/1.03  # Proof object clause steps            : 74
% 0.88/1.03  # Proof object formula steps           : 39
% 0.88/1.03  # Proof object conjectures             : 39
% 0.88/1.03  # Proof object clause conjectures      : 36
% 0.88/1.03  # Proof object formula conjectures     : 3
% 0.88/1.03  # Proof object initial clauses used    : 26
% 0.88/1.03  # Proof object initial formulas used   : 19
% 0.88/1.03  # Proof object generating inferences   : 42
% 0.88/1.03  # Proof object simplifying inferences  : 73
% 0.88/1.03  # Training examples: 0 positive, 0 negative
% 0.88/1.03  # Parsed axioms                        : 19
% 0.88/1.03  # Removed by relevancy pruning/SinE    : 0
% 0.88/1.03  # Initial clauses                      : 34
% 0.88/1.03  # Removed in clause preprocessing      : 1
% 0.88/1.03  # Initial clauses in saturation        : 33
% 0.88/1.03  # Processed clauses                    : 5635
% 0.88/1.03  # ...of these trivial                  : 35
% 0.88/1.03  # ...subsumed                          : 4639
% 0.88/1.03  # ...remaining for further processing  : 961
% 0.88/1.03  # Other redundant clauses eliminated   : 49
% 0.88/1.03  # Clauses deleted for lack of memory   : 0
% 0.88/1.03  # Backward-subsumed                    : 80
% 0.88/1.03  # Backward-rewritten                   : 32
% 0.88/1.03  # Generated clauses                    : 29837
% 0.88/1.03  # ...of the previous two non-trivial   : 27036
% 0.88/1.03  # Contextual simplify-reflections      : 220
% 0.88/1.03  # Paramodulations                      : 29749
% 0.88/1.03  # Factorizations                       : 0
% 0.88/1.03  # Equation resolutions                 : 87
% 0.88/1.03  # Propositional unsat checks           : 0
% 0.88/1.03  #    Propositional check models        : 0
% 0.88/1.03  #    Propositional check unsatisfiable : 0
% 0.88/1.03  #    Propositional clauses             : 0
% 0.88/1.03  #    Propositional clauses after purity: 0
% 0.88/1.03  #    Propositional unsat core size     : 0
% 0.88/1.03  #    Propositional preprocessing time  : 0.000
% 0.88/1.03  #    Propositional encoding time       : 0.000
% 0.88/1.03  #    Propositional solver time         : 0.000
% 0.88/1.03  #    Success case prop preproc time    : 0.000
% 0.88/1.03  #    Success case prop encoding time   : 0.000
% 0.88/1.03  #    Success case prop solver time     : 0.000
% 0.88/1.03  # Current number of processed clauses  : 811
% 0.88/1.03  #    Positive orientable unit clauses  : 26
% 0.88/1.03  #    Positive unorientable unit clauses: 0
% 0.88/1.03  #    Negative unit clauses             : 9
% 0.88/1.03  #    Non-unit-clauses                  : 776
% 0.88/1.03  # Current number of unprocessed clauses: 21355
% 0.88/1.03  # ...number of literals in the above   : 91724
% 0.88/1.03  # Current number of archived formulas  : 0
% 0.88/1.03  # Current number of archived clauses   : 145
% 0.88/1.03  # Clause-clause subsumption calls (NU) : 190812
% 0.88/1.03  # Rec. Clause-clause subsumption calls : 113447
% 0.88/1.03  # Non-unit clause-clause subsumptions  : 4784
% 0.88/1.03  # Unit Clause-clause subsumption calls : 1890
% 0.88/1.03  # Rewrite failures with RHS unbound    : 0
% 0.88/1.03  # BW rewrite match attempts            : 44
% 0.88/1.03  # BW rewrite match successes           : 8
% 0.88/1.03  # Condensation attempts                : 0
% 0.88/1.03  # Condensation successes               : 0
% 0.88/1.03  # Termbank termtop insertions          : 1150627
% 0.88/1.03  
% 0.88/1.03  # -------------------------------------------------
% 0.88/1.03  # User time                : 0.679 s
% 0.88/1.03  # System time              : 0.015 s
% 0.88/1.03  # Total time               : 0.694 s
% 0.88/1.03  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

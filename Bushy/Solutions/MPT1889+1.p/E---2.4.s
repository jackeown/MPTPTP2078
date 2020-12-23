%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t57_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:54 EDT 2019

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 231 expanded)
%              Number of clauses        :   32 (  82 expanded)
%              Number of leaves         :    8 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 (1757 expanded)
%              Number of equality atoms :   22 ( 143 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',t57_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',t4_subset)).

fof(t37_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',t37_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',dt_l1_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',redefinition_k6_domain_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',redefinition_k9_subset_1)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t57_tex_2.p',t24_tdlat_3)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v4_pre_topc(X4,X1)
                              & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
             => v2_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_tex_2])).

fof(c_0_9,plain,(
    ! [X224,X225,X226] :
      ( ~ r2_hidden(X224,X225)
      | ~ m1_subset_1(X225,k1_zfmisc_1(X226))
      | m1_subset_1(X224,X226) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_10,negated_conjecture,(
    ! [X7] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & v3_tdlat_3(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(X7,esk2_0)
        | ~ m1_subset_1(X7,u1_struct_0(esk1_0)) )
      & ( v4_pre_topc(esk3_1(X7),esk1_0)
        | ~ r2_hidden(X7,esk2_0)
        | ~ m1_subset_1(X7,u1_struct_0(esk1_0)) )
      & ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_1(X7)) = k6_domain_1(u1_struct_0(esk1_0),X7)
        | ~ r2_hidden(X7,esk2_0)
        | ~ m1_subset_1(X7,u1_struct_0(esk1_0)) )
      & ~ v2_tex_2(esk2_0,esk1_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_11,plain,(
    ! [X218,X219,X221] :
      ( ( m1_subset_1(esk47_2(X218,X219),u1_struct_0(X218))
        | v2_tex_2(X219,X218)
        | ~ m1_subset_1(X219,k1_zfmisc_1(u1_struct_0(X218)))
        | v2_struct_0(X218)
        | ~ v2_pre_topc(X218)
        | ~ l1_pre_topc(X218) )
      & ( r2_hidden(esk47_2(X218,X219),X219)
        | v2_tex_2(X219,X218)
        | ~ m1_subset_1(X219,k1_zfmisc_1(u1_struct_0(X218)))
        | v2_struct_0(X218)
        | ~ v2_pre_topc(X218)
        | ~ l1_pre_topc(X218) )
      & ( ~ m1_subset_1(X221,k1_zfmisc_1(u1_struct_0(X218)))
        | ~ v3_pre_topc(X221,X218)
        | k9_subset_1(u1_struct_0(X218),X219,X221) != k6_domain_1(u1_struct_0(X218),esk47_2(X218,X219))
        | v2_tex_2(X219,X218)
        | ~ m1_subset_1(X219,k1_zfmisc_1(u1_struct_0(X218)))
        | v2_struct_0(X218)
        | ~ v2_pre_topc(X218)
        | ~ l1_pre_topc(X218) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).

fof(c_0_12,plain,(
    ! [X126] :
      ( v2_struct_0(X126)
      | ~ l1_struct_0(X126)
      | ~ v1_xboole_0(u1_struct_0(X126)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_13,plain,(
    ! [X114] :
      ( ~ l1_pre_topc(X114)
      | l1_struct_0(X114) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk47_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X205,X206] :
      ( v1_xboole_0(X205)
      | ~ m1_subset_1(X206,X205)
      | k6_domain_1(X205,X206) = k1_tarski(X206) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk47_2(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk47_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_17])])).

cnf(c_0_30,plain,
    ( v2_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != k6_domain_1(u1_struct_0(X2),esk47_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk47_2(esk1_0,esk2_0)) = k1_tarski(esk47_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_32,plain,(
    ! [X207,X208,X209] :
      ( ~ m1_subset_1(X209,k1_zfmisc_1(X207))
      | k9_subset_1(X207,X208,X209) = k3_xboole_0(X208,X209) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_33,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) != k1_tarski(esk47_2(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_15]),c_0_17]),c_0_18])]),c_0_19]),c_0_20]),c_0_31])).

cnf(c_0_34,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_1(X1)) = k6_domain_1(u1_struct_0(esk1_0),X1)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) != k1_tarski(esk47_2(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_1(X1)) = k6_domain_1(u1_struct_0(esk1_0),X1)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),X1) != k1_tarski(esk47_2(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk3_1(X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_40,plain,(
    ! [X212,X213] :
      ( ( ~ v3_tdlat_3(X212)
        | ~ m1_subset_1(X213,k1_zfmisc_1(u1_struct_0(X212)))
        | ~ v4_pre_topc(X213,X212)
        | v3_pre_topc(X213,X212)
        | ~ v2_pre_topc(X212)
        | ~ l1_pre_topc(X212) )
      & ( m1_subset_1(esk46_1(X212),k1_zfmisc_1(u1_struct_0(X212)))
        | v3_tdlat_3(X212)
        | ~ v2_pre_topc(X212)
        | ~ l1_pre_topc(X212) )
      & ( v4_pre_topc(esk46_1(X212),X212)
        | v3_tdlat_3(X212)
        | ~ v2_pre_topc(X212)
        | ~ l1_pre_topc(X212) )
      & ( ~ v3_pre_topc(esk46_1(X212),X212)
        | v3_tdlat_3(X212)
        | ~ v2_pre_topc(X212)
        | ~ l1_pre_topc(X212) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_41,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),X1) != k1_tarski(esk47_2(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk3_1(X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24])).

cnf(c_0_42,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( v3_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),X1) != k1_tarski(esk47_2(esk1_0,esk2_0))
    | ~ v4_pre_topc(esk3_1(X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_17]),c_0_43]),c_0_18])])).

cnf(c_0_45,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),X1) != k1_tarski(esk47_2(esk1_0,esk2_0))
    | ~ v4_pre_topc(esk3_1(X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_39]),c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( v4_pre_topc(esk3_1(X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),X1) != k1_tarski(esk47_2(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------

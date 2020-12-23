%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 215 expanded)
%              Number of clauses        :   23 (  70 expanded)
%              Number of leaves         :    4 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 (1880 expanded)
%              Number of equality atoms :   10 ( 140 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(c_0_4,negated_conjecture,(
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

fof(c_0_5,plain,(
    ! [X8,X9,X11] :
      ( ( m1_subset_1(esk2_2(X8,X9),u1_struct_0(X8))
        | v2_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | v2_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_pre_topc(X11,X8)
        | k9_subset_1(u1_struct_0(X8),X9,X11) != k6_domain_1(u1_struct_0(X8),esk2_2(X8,X9))
        | v2_tex_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X17] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & v3_tdlat_3(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_1(X17),k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r2_hidden(X17,esk4_0)
        | ~ m1_subset_1(X17,u1_struct_0(esk3_0)) )
      & ( v4_pre_topc(esk5_1(X17),esk3_0)
        | ~ r2_hidden(X17,esk4_0)
        | ~ m1_subset_1(X17,u1_struct_0(esk3_0)) )
      & ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_1(X17)) = k6_domain_1(u1_struct_0(esk3_0),X17)
        | ~ r2_hidden(X17,esk4_0)
        | ~ m1_subset_1(X17,u1_struct_0(esk3_0)) )
      & ~ v2_tex_2(esk4_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_8,plain,
    ( v2_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != k6_domain_1(u1_struct_0(X2),esk2_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),c_0_12]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_1(X1)) = k6_domain_1(u1_struct_0(esk3_0),X1)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ v3_pre_topc(esk5_1(X1),esk3_0)
    | ~ m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ v3_pre_topc(esk5_1(X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_2(esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_9]),c_0_10]),c_0_11])]),c_0_12]),c_0_13])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ( ~ v3_tdlat_3(X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v4_pre_topc(X6,X5)
        | v3_pre_topc(X6,X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_1(X5),k1_zfmisc_1(u1_struct_0(X5)))
        | v3_tdlat_3(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( v4_pre_topc(esk1_1(X5),X5)
        | v3_tdlat_3(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ v3_pre_topc(esk1_1(X5),X5)
        | v3_tdlat_3(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v3_pre_topc(esk5_1(esk2_2(esk3_0,esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])])).

cnf(c_0_25,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( ~ v4_pre_topc(esk5_1(esk2_2(esk3_0,esk4_0)),esk3_0)
    | ~ m1_subset_1(esk5_1(esk2_2(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_10]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( v4_pre_topc(esk5_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_2(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(esk5_1(esk2_2(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22]),c_0_29])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_22]),c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------

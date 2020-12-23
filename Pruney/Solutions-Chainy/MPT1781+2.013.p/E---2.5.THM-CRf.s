%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  120 (4802 expanded)
%              Number of clauses        :   91 (1605 expanded)
%              Number of leaves         :   14 (1185 expanded)
%              Depth                    :   22
%              Number of atoms          :  575 (38650 expanded)
%              Number of equality atoms :   35 (2675 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,u1_struct_0(X2))
                     => X4 = k1_funct_1(X3,X4) ) )
               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(t59_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(t95_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,u1_struct_0(X2))
               => k1_funct_1(k4_tmap_1(X1,X2),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,u1_struct_0(X2))
                       => X4 = k1_funct_1(X3,X4) ) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t96_tmap_1])).

fof(c_0_15,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ( m1_subset_1(esk1_5(X35,X36,X37,X38,X39),u1_struct_0(X36))
        | r2_funct_2(u1_struct_0(X37),u1_struct_0(X35),k2_tmap_1(X36,X35,X38,X37),X39)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X35))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35))))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk1_5(X35,X36,X37,X38,X39),u1_struct_0(X37))
        | r2_funct_2(u1_struct_0(X37),u1_struct_0(X35),k2_tmap_1(X36,X35,X38,X37),X39)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X35))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35))))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( k3_funct_2(u1_struct_0(X36),u1_struct_0(X35),X38,esk1_5(X35,X36,X37,X38,X39)) != k1_funct_1(X39,esk1_5(X35,X36,X37,X38,X39))
        | r2_funct_2(u1_struct_0(X37),u1_struct_0(X35),k2_tmap_1(X36,X35,X38,X37),X39)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X35))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35))))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

fof(c_0_16,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | m1_pre_topc(X34,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_17,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_18,negated_conjecture,(
    ! [X47] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X47,u1_struct_0(esk2_0))
        | ~ r2_hidden(X47,u1_struct_0(esk3_0))
        | X47 = k1_funct_1(esk4_0,X47) )
      & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | v2_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X3))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X2),X4)
    | r2_hidden(esk1_5(X1,X2,X2,X3,X4),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24]),c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_35,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | m1_subset_1(u1_struct_0(X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_37,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | ~ v1_xboole_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_38,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),esk4_0)
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,X1,esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_24]),c_0_30]),c_0_26]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X10,X11,X12,X13] :
      ( v1_xboole_0(X10)
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,X10,X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(X13,X10)
      | k3_funct_2(X10,X11,X12,X13) = k1_funct_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X2),X4)
    | m1_subset_1(esk1_5(X1,X2,X2,X3,X4),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_21])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_44,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21])).

fof(c_0_45,plain,(
    ! [X26,X27,X28,X29] :
      ( ( v1_funct_1(k2_tmap_1(X26,X27,X28,X29))
        | ~ l1_struct_0(X26)
        | ~ l1_struct_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_struct_0(X29) )
      & ( v1_funct_2(k2_tmap_1(X26,X27,X28,X29),u1_struct_0(X29),u1_struct_0(X27))
        | ~ l1_struct_0(X26)
        | ~ l1_struct_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_struct_0(X29) )
      & ( m1_subset_1(k2_tmap_1(X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X27))))
        | ~ l1_struct_0(X26)
        | ~ l1_struct_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
        | ~ l1_struct_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),esk4_0)
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,X1,esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_29]),c_0_24]),c_0_30]),c_0_26]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

fof(c_0_50,plain,(
    ! [X30,X31] :
      ( ( v1_funct_1(k4_tmap_1(X30,X31))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) )
      & ( v1_funct_2(k4_tmap_1(X30,X31),u1_struct_0(X31),u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) )
      & ( m1_subset_1(k4_tmap_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

cnf(c_0_51,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,X1) = k1_funct_1(esk4_0,X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_62,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_65,plain,
    ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X2,X1,X4,X3,X5)) != k1_funct_1(X5,esk1_5(X2,X1,X4,X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0)) = k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_23]),c_0_24]),c_0_26])]),c_0_33])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_23]),c_0_24]),c_0_26])]),c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_23]),c_0_24]),c_0_26])]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_24])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_62]),c_0_24])])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_62]),c_0_24])])).

fof(c_0_73,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r2_funct_2(X14,X15,X16,X17)
        | X16 = X17
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X16 != X17
        | r2_funct_2(X14,X15,X16,X17)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_24]),c_0_29]),c_0_26]),c_0_30]),c_0_28]),c_0_31]),c_0_32])]),c_0_34]),c_0_33])).

cnf(c_0_75,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_67]),c_0_29]),c_0_24]),c_0_30]),c_0_26]),c_0_68]),c_0_69])]),c_0_33]),c_0_34])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_62]),c_0_29])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_62]),c_0_29])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_62]),c_0_29])])).

cnf(c_0_79,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_21]),c_0_29])])).

cnf(c_0_81,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0) = esk4_0
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_83,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_62]),c_0_29])])).

cnf(c_0_84,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_67]),c_0_29]),c_0_24]),c_0_30]),c_0_26]),c_0_68]),c_0_69])]),c_0_33]),c_0_34])).

cnf(c_0_85,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0) = esk4_0
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_83])).

fof(c_0_87,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | m1_subset_1(X25,u1_struct_0(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_88,plain,(
    ! [X41,X42,X43] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | v2_struct_0(X42)
      | ~ m1_pre_topc(X42,X41)
      | ~ m1_subset_1(X43,u1_struct_0(X41))
      | ~ r2_hidden(X43,u1_struct_0(X42))
      | k1_funct_1(k4_tmap_1(X41,X42),X43) = X43 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_89,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_90,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_62]),c_0_29])])).

cnf(c_0_91,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_49])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_93,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_31]),c_0_32])])).

cnf(c_0_95,negated_conjecture,
    ( k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),X2) = k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),X2)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_90]),c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( X1 = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_23]),c_0_24])]),c_0_34]),c_0_33])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(X1,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_34])).

cnf(c_0_101,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_90]),c_0_90]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_89])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_23]),c_0_24]),c_0_26])]),c_0_33])).

cnf(c_0_105,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_62]),c_0_29])])).

cnf(c_0_106,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) != k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_105]),c_0_90]),c_0_24]),c_0_29]),c_0_26]),c_0_30]),c_0_67]),c_0_28]),c_0_68]),c_0_31]),c_0_69]),c_0_32])]),c_0_34]),c_0_33])).

cnf(c_0_109,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_106,c_0_90])).

cnf(c_0_110,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_107,c_0_90])).

cnf(c_0_111,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_112,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])).

cnf(c_0_113,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_111])).

cnf(c_0_114,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_21]),c_0_29])])).

cnf(c_0_115,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_67]),c_0_68])])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = k4_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_114]),c_0_67]),c_0_28]),c_0_68]),c_0_31]),c_0_69]),c_0_32])])).

cnf(c_0_118,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_69])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117]),c_0_118])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.43  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.029 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.19/0.43  fof(t59_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.19/0.43  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.43  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.43  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.43  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.43  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.43  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.19/0.43  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.19/0.43  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.19/0.43  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.43  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.19/0.43  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.19/0.43  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.19/0.43  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.19/0.43  fof(c_0_15, plain, ![X35, X36, X37, X38, X39]:((m1_subset_1(esk1_5(X35,X36,X37,X38,X39),u1_struct_0(X36))|r2_funct_2(u1_struct_0(X37),u1_struct_0(X35),k2_tmap_1(X36,X35,X38,X37),X39)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X35))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35)))))|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))))|(v2_struct_0(X37)|~m1_pre_topc(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&((r2_hidden(esk1_5(X35,X36,X37,X38,X39),u1_struct_0(X37))|r2_funct_2(u1_struct_0(X37),u1_struct_0(X35),k2_tmap_1(X36,X35,X38,X37),X39)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X35))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35)))))|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))))|(v2_struct_0(X37)|~m1_pre_topc(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(k3_funct_2(u1_struct_0(X36),u1_struct_0(X35),X38,esk1_5(X35,X36,X37,X38,X39))!=k1_funct_1(X39,esk1_5(X35,X36,X37,X38,X39))|r2_funct_2(u1_struct_0(X37),u1_struct_0(X35),k2_tmap_1(X36,X35,X38,X37),X39)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X35))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35)))))|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))))|(v2_struct_0(X37)|~m1_pre_topc(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).
% 0.19/0.43  fof(c_0_16, plain, ![X34]:(~l1_pre_topc(X34)|m1_pre_topc(X34,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.43  fof(c_0_17, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.43  fof(c_0_18, negated_conjecture, ![X47]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X47,u1_struct_0(esk2_0))|(~r2_hidden(X47,u1_struct_0(esk3_0))|X47=k1_funct_1(esk4_0,X47)))&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.19/0.43  fof(c_0_19, plain, ![X18, X19]:(~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|v2_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.43  cnf(c_0_20, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X3))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_21, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_22, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_25, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.43  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X2),X4)|r2_hidden(esk1_5(X1,X2,X2,X3,X4),u1_struct_0(X2))|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.43  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.43  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_24]), c_0_26])])).
% 0.19/0.43  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  fof(c_0_35, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_pre_topc(X33,X32)|m1_subset_1(u1_struct_0(X33),k1_zfmisc_1(u1_struct_0(X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.43  cnf(c_0_36, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  fof(c_0_37, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|~v1_xboole_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),esk4_0)|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,X1,esk4_0),u1_struct_0(esk3_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_24]), c_0_30]), c_0_26]), c_0_31]), c_0_32])]), c_0_33]), c_0_34])).
% 0.19/0.43  cnf(c_0_39, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.43  fof(c_0_40, plain, ![X10, X11, X12, X13]:(v1_xboole_0(X10)|~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~m1_subset_1(X13,X10)|k3_funct_2(X10,X11,X12,X13)=k1_funct_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.19/0.43  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X2),X4)|m1_subset_1(esk1_5(X1,X2,X2,X3,X4),u1_struct_0(X2))|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_36, c_0_21])).
% 0.19/0.43  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_44, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_21])).
% 0.19/0.43  fof(c_0_45, plain, ![X26, X27, X28, X29]:(((v1_funct_1(k2_tmap_1(X26,X27,X28,X29))|(~l1_struct_0(X26)|~l1_struct_0(X27)|~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))|~l1_struct_0(X29)))&(v1_funct_2(k2_tmap_1(X26,X27,X28,X29),u1_struct_0(X29),u1_struct_0(X27))|(~l1_struct_0(X26)|~l1_struct_0(X27)|~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))|~l1_struct_0(X29))))&(m1_subset_1(k2_tmap_1(X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X27))))|(~l1_struct_0(X26)|~l1_struct_0(X27)|~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))|~l1_struct_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.19/0.43  cnf(c_0_46, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.43  cnf(c_0_47, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),esk4_0)|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,X1,esk4_0),u1_struct_0(esk3_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_29]), c_0_24]), c_0_30]), c_0_26]), c_0_31]), c_0_32])]), c_0_33]), c_0_34])).
% 0.19/0.43  cnf(c_0_48, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)|~v1_xboole_0(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 0.19/0.43  fof(c_0_50, plain, ![X30, X31]:(((v1_funct_1(k4_tmap_1(X30,X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30)))&(v1_funct_2(k4_tmap_1(X30,X31),u1_struct_0(X31),u1_struct_0(X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30))))&(m1_subset_1(k4_tmap_1(X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.19/0.43  cnf(c_0_51, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  fof(c_0_52, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.43  cnf(c_0_53, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  cnf(c_0_54, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  cnf(c_0_55, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,X1)=k1_funct_1(esk4_0,X1)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_57, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.43  cnf(c_0_58, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.43  cnf(c_0_59, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.43  cnf(c_0_60, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_62, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_65, plain, (r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X2,X1,X4,X3,X5))!=k1_funct_1(X5,esk1_5(X2,X1,X4,X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_66, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0))=k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,esk4_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.19/0.43  cnf(c_0_67, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_23]), c_0_24]), c_0_26])]), c_0_33])).
% 0.19/0.43  cnf(c_0_68, negated_conjecture, (v1_funct_1(k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_23]), c_0_24]), c_0_26])]), c_0_33])).
% 0.19/0.43  cnf(c_0_69, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_23]), c_0_24]), c_0_26])]), c_0_33])).
% 0.19/0.43  cnf(c_0_70, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_24])])).
% 0.19/0.43  cnf(c_0_71, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_62]), c_0_24])])).
% 0.19/0.43  cnf(c_0_72, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_62]), c_0_24])])).
% 0.19/0.43  fof(c_0_73, plain, ![X14, X15, X16, X17]:((~r2_funct_2(X14,X15,X16,X17)|X16=X17|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))&(X16!=X17|r2_funct_2(X14,X15,X16,X17)|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.19/0.43  cnf(c_0_74, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_24]), c_0_29]), c_0_26]), c_0_30]), c_0_28]), c_0_31]), c_0_32])]), c_0_34]), c_0_33])).
% 0.19/0.43  cnf(c_0_75, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),k4_tmap_1(esk2_0,esk3_0))|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_67]), c_0_29]), c_0_24]), c_0_30]), c_0_26]), c_0_68]), c_0_69])]), c_0_33]), c_0_34])).
% 0.19/0.43  cnf(c_0_76, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_62]), c_0_29])])).
% 0.19/0.43  cnf(c_0_77, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_62]), c_0_29])])).
% 0.19/0.43  cnf(c_0_78, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_62]), c_0_29])])).
% 0.19/0.43  cnf(c_0_79, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.43  cnf(c_0_80, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_21]), c_0_29])])).
% 0.19/0.43  cnf(c_0_81, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])).
% 0.19/0.43  cnf(c_0_82, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0)=esk4_0|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_83, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_62]), c_0_29])])).
% 0.19/0.43  cnf(c_0_84, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,X1,esk3_0),k4_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_67]), c_0_29]), c_0_24]), c_0_30]), c_0_26]), c_0_68]), c_0_69])]), c_0_33]), c_0_34])).
% 0.19/0.43  cnf(c_0_85, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0)=esk4_0|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_76]), c_0_77]), c_0_78])).
% 0.19/0.43  cnf(c_0_86, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))|~v1_xboole_0(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_83])).
% 0.19/0.43  fof(c_0_87, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~m1_pre_topc(X24,X23)|(~m1_subset_1(X25,u1_struct_0(X24))|m1_subset_1(X25,u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.19/0.43  fof(c_0_88, plain, ![X41, X42, X43]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(v2_struct_0(X42)|~m1_pre_topc(X42,X41)|(~m1_subset_1(X43,u1_struct_0(X41))|(~r2_hidden(X43,u1_struct_0(X42))|k1_funct_1(k4_tmap_1(X41,X42),X43)=X43)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.19/0.43  cnf(c_0_89, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_90, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_62]), c_0_29])])).
% 0.19/0.43  cnf(c_0_91, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),esk3_0),k4_tmap_1(esk2_0,esk3_0))|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_86, c_0_49])).
% 0.19/0.43  cnf(c_0_92, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.43  cnf(c_0_93, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.43  cnf(c_0_94, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_28]), c_0_31]), c_0_32])])).
% 0.19/0.43  cnf(c_0_95, negated_conjecture, (k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),X2)=k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),X2)|v1_xboole_0(u1_struct_0(X1))|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_76]), c_0_77]), c_0_78])).
% 0.19/0.43  cnf(c_0_96, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.43  cnf(c_0_97, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))|~v1_xboole_0(u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_90]), c_0_90])).
% 0.19/0.43  cnf(c_0_98, negated_conjecture, (X1=k1_funct_1(esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_99, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_23]), c_0_24])]), c_0_34]), c_0_33])).
% 0.19/0.43  cnf(c_0_100, negated_conjecture, (k1_funct_1(k4_tmap_1(X1,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_34])).
% 0.19/0.43  cnf(c_0_101, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_90]), c_0_90]), c_0_97])).
% 0.19/0.43  cnf(c_0_102, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_98, c_0_94])).
% 0.19/0.43  cnf(c_0_103, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_99, c_0_89])).
% 0.19/0.43  cnf(c_0_104, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))|~m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_23]), c_0_24]), c_0_26])]), c_0_33])).
% 0.19/0.43  cnf(c_0_105, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_62]), c_0_29])])).
% 0.19/0.43  cnf(c_0_106, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.19/0.43  cnf(c_0_107, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk4_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_104, c_0_103])).
% 0.19/0.43  cnf(c_0_108, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))|k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))!=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_105]), c_0_90]), c_0_24]), c_0_29]), c_0_26]), c_0_30]), c_0_67]), c_0_28]), c_0_68]), c_0_31]), c_0_69]), c_0_32])]), c_0_34]), c_0_33])).
% 0.19/0.43  cnf(c_0_109, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_106, c_0_90])).
% 0.19/0.43  cnf(c_0_110, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_5(esk2_0,esk3_0,esk3_0,esk4_0,k4_tmap_1(esk2_0,esk3_0))|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_107, c_0_90])).
% 0.19/0.43  cnf(c_0_111, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.43  cnf(c_0_112, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])).
% 0.19/0.43  cnf(c_0_113, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_111])).
% 0.19/0.43  cnf(c_0_114, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_21]), c_0_29])])).
% 0.19/0.43  cnf(c_0_115, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_67]), c_0_68])])).
% 0.19/0.43  cnf(c_0_116, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_117, negated_conjecture, (esk4_0=k4_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_114]), c_0_67]), c_0_28]), c_0_68]), c_0_31]), c_0_69]), c_0_32])])).
% 0.19/0.43  cnf(c_0_118, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_69])])).
% 0.19/0.43  cnf(c_0_119, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117]), c_0_118])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 120
% 0.19/0.43  # Proof object clause steps            : 91
% 0.19/0.43  # Proof object formula steps           : 29
% 0.19/0.43  # Proof object conjectures             : 70
% 0.19/0.43  # Proof object clause conjectures      : 67
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 30
% 0.19/0.43  # Proof object initial formulas used   : 14
% 0.19/0.43  # Proof object generating inferences   : 54
% 0.19/0.43  # Proof object simplifying inferences  : 167
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 14
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 30
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 30
% 0.19/0.43  # Processed clauses                    : 379
% 0.19/0.43  # ...of these trivial                  : 0
% 0.19/0.43  # ...subsumed                          : 21
% 0.19/0.43  # ...remaining for further processing  : 358
% 0.19/0.43  # Other redundant clauses eliminated   : 1
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 82
% 0.19/0.43  # Backward-rewritten                   : 141
% 0.19/0.43  # Generated clauses                    : 536
% 0.19/0.43  # ...of the previous two non-trivial   : 632
% 0.19/0.43  # Contextual simplify-reflections      : 111
% 0.19/0.43  # Paramodulations                      : 535
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 1
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 104
% 0.19/0.43  #    Positive orientable unit clauses  : 13
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 2
% 0.19/0.43  #    Non-unit-clauses                  : 89
% 0.19/0.43  # Current number of unprocessed clauses: 233
% 0.19/0.43  # ...number of literals in the above   : 1364
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 253
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 14433
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 4363
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 214
% 0.19/0.43  # Unit Clause-clause subsumption calls : 196
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 70
% 0.19/0.43  # BW rewrite match successes           : 5
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 34958
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.088 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.093 s
% 0.19/0.43  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

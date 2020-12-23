%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 (5568 expanded)
%              Number of clauses        :   88 (1825 expanded)
%              Number of leaves         :   18 (1381 expanded)
%              Depth                    :   23
%              Number of atoms          :  641 (44866 expanded)
%              Number of equality atoms :   45 (3095 expanded)
%              Maximal formula depth    :   24 (   6 average)
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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

fof(t74_tmap_1,axiom,(
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
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X37,X38] :
      ( ( v1_funct_1(k4_tmap_1(X37,X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( v1_funct_2(k4_tmap_1(X37,X38),u1_struct_0(X38),u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) )
      & ( m1_subset_1(k4_tmap_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X38,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_20,negated_conjecture,(
    ! [X64] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X64,u1_struct_0(esk2_0))
        | ~ r2_hidden(X64,u1_struct_0(esk3_0))
        | X64 = k1_funct_1(esk4_0,X64) )
      & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).

fof(c_0_21,plain,(
    ! [X33,X34,X35,X36] :
      ( ( v1_funct_1(k2_tmap_1(X33,X34,X35,X36))
        | ~ l1_struct_0(X33)
        | ~ l1_struct_0(X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
        | ~ l1_struct_0(X36) )
      & ( v1_funct_2(k2_tmap_1(X33,X34,X35,X36),u1_struct_0(X36),u1_struct_0(X34))
        | ~ l1_struct_0(X33)
        | ~ l1_struct_0(X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
        | ~ l1_struct_0(X36) )
      & ( m1_subset_1(k2_tmap_1(X33,X34,X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X34))))
        | ~ l1_struct_0(X33)
        | ~ l1_struct_0(X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
        | ~ l1_struct_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_33,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_34,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X18,X19] :
      ( ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | v2_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_24])])).

cnf(c_0_41,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_42,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X28)
      | ~ m1_pre_topc(X31,X28)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))
      | ~ m1_pre_topc(X31,X30)
      | k3_tmap_1(X28,X29,X30,X31,X32) = k2_partfun1(u1_struct_0(X30),u1_struct_0(X29),X32,u1_struct_0(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_43,plain,(
    ! [X55,X56,X57] :
      ( ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_pre_topc(X56,X55)
      | ~ m1_pre_topc(X57,X56)
      | m1_pre_topc(X57,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_44,plain,(
    ! [X24,X25,X26,X27] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ v1_funct_1(X26)
      | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
      | ~ m1_pre_topc(X27,X24)
      | k2_tmap_1(X24,X25,X26,X27) = k2_partfun1(u1_struct_0(X24),u1_struct_0(X25),X26,u1_struct_0(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_45,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_36]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_48,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_54,plain,(
    ! [X41] :
      ( ~ l1_pre_topc(X41)
      | m1_pre_topc(X41,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_55,plain,(
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

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_36]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_31]),c_0_32])])).

fof(c_0_59,plain,(
    ! [X51,X52,X53,X54] :
      ( v2_struct_0(X51)
      | ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | v2_struct_0(X52)
      | ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | v2_struct_0(X53)
      | ~ m1_pre_topc(X53,X51)
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,u1_struct_0(X53),u1_struct_0(X52))
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X52))))
      | r2_funct_2(u1_struct_0(X53),u1_struct_0(X52),X54,k3_tmap_1(X51,X52,X53,X53,X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).

cnf(c_0_60,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_30]),c_0_24]),c_0_40]),c_0_25]),c_0_52]),c_0_31]),c_0_32])]),c_0_26]),c_0_53])).

cnf(c_0_62,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_40])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_40])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_36]),c_0_24])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_30]),c_0_24]),c_0_25]),c_0_31]),c_0_32])]),c_0_26])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)) = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_40])])).

cnf(c_0_70,negated_conjecture,
    ( X1 = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_36]),c_0_40])])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_30]),c_0_24]),c_0_25]),c_0_31]),c_0_32])]),c_0_53]),c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_62]),c_0_69]),c_0_40])])).

fof(c_0_75,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X39)
      | m1_subset_1(u1_struct_0(X40),k1_zfmisc_1(u1_struct_0(X39))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_76,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( ( m1_subset_1(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X46))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( r2_hidden(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X47))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( k3_funct_2(u1_struct_0(X46),u1_struct_0(X45),X48,esk1_5(X45,X46,X47,X48,X49)) != k1_funct_1(X49,esk1_5(X45,X46,X47,X48,X49))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

cnf(c_0_77,negated_conjecture,
    ( X1 = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_40])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_62]),c_0_40]),c_0_52])]),c_0_53])).

cnf(c_0_80,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_62]),c_0_40]),c_0_52])]),c_0_53])).

cnf(c_0_81,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_82,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | m1_subset_1(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_83,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_87,negated_conjecture,
    ( X1 = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_40])])).

cnf(c_0_88,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_89,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_62])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_23]),c_0_24])])).

cnf(c_0_92,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)
    | r2_hidden(esk1_5(esk2_0,X1,esk3_0,X2,esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_24]),c_0_25]),c_0_85]),c_0_86])]),c_0_53]),c_0_26])).

cnf(c_0_93,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0) = k4_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_31]),c_0_32]),c_0_30])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_40])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_30]),c_0_93]),c_0_40]),c_0_52]),c_0_31]),c_0_32])]),c_0_53]),c_0_94])).

fof(c_0_98,plain,(
    ! [X10,X11,X12,X13] :
      ( v1_xboole_0(X10)
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,X10,X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(X13,X10)
      | k3_funct_2(X10,X11,X12,X13) = k1_funct_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_95])).

fof(c_0_100,plain,(
    ! [X58,X59,X60] :
      ( v2_struct_0(X58)
      | ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | v2_struct_0(X59)
      | ~ m1_pre_topc(X59,X58)
      | ~ m1_subset_1(X60,u1_struct_0(X58))
      | ~ r2_hidden(X60,u1_struct_0(X59))
      | k1_funct_1(k4_tmap_1(X58,X59),X60) = X60 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_97])).

cnf(c_0_104,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_62]),c_0_40])])).

fof(c_0_106,plain,(
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l1_struct_0(X23)
      | ~ v1_xboole_0(u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_107,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1) = k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_30]),c_0_32])]),c_0_31])])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_62]),c_0_40])])).

cnf(c_0_109,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,X1),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_110,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_97]),c_0_23])]),c_0_53])).

cnf(c_0_113,negated_conjecture,
    ( X1 = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_114,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_53])).

cnf(c_0_115,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_62]),c_0_40])])).

cnf(c_0_116,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_105])).

cnf(c_0_117,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_118,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_97])).

cnf(c_0_120,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0)) != k1_funct_1(esk4_0,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_84]),c_0_24]),c_0_25]),c_0_85]),c_0_86])]),c_0_53]),c_0_26])).

cnf(c_0_121,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_36]),c_0_40])])).

cnf(c_0_122,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_62]),c_0_40])])).

cnf(c_0_123,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_30]),c_0_93]),c_0_121]),c_0_122]),c_0_40]),c_0_52]),c_0_31]),c_0_32])]),c_0_53]),c_0_94])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_62]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:25:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 0.20/0.43  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.030 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.20/0.43  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.20/0.43  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.20/0.43  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.43  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.43  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.43  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.43  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.43  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.43  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.43  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.20/0.43  fof(t74_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 0.20/0.43  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.43  fof(t59_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.20/0.43  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.43  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.20/0.43  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.20/0.43  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.43  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.20/0.43  fof(c_0_19, plain, ![X37, X38]:(((v1_funct_1(k4_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))&(v1_funct_2(k4_tmap_1(X37,X38),u1_struct_0(X38),u1_struct_0(X37))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37))))&(m1_subset_1(k4_tmap_1(X37,X38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.20/0.43  fof(c_0_20, negated_conjecture, ![X64]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X64,u1_struct_0(esk2_0))|(~r2_hidden(X64,u1_struct_0(esk3_0))|X64=k1_funct_1(esk4_0,X64)))&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).
% 0.20/0.43  fof(c_0_21, plain, ![X33, X34, X35, X36]:(((v1_funct_1(k2_tmap_1(X33,X34,X35,X36))|(~l1_struct_0(X33)|~l1_struct_0(X34)|~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))|~l1_struct_0(X36)))&(v1_funct_2(k2_tmap_1(X33,X34,X35,X36),u1_struct_0(X36),u1_struct_0(X34))|(~l1_struct_0(X33)|~l1_struct_0(X34)|~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))|~l1_struct_0(X36))))&(m1_subset_1(k2_tmap_1(X33,X34,X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X34))))|(~l1_struct_0(X33)|~l1_struct_0(X34)|~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))|~l1_struct_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.20/0.43  cnf(c_0_22, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_27, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_28, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_29, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (v1_funct_1(k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.43  fof(c_0_33, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.43  fof(c_0_34, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.20/0.43  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_37, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.43  fof(c_0_38, plain, ![X18, X19]:(~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|v2_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24])])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_23]), c_0_24])])).
% 0.20/0.43  cnf(c_0_41, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  fof(c_0_42, plain, ![X28, X29, X30, X31, X32]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_pre_topc(X30,X28)|(~m1_pre_topc(X31,X28)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))|(~m1_pre_topc(X31,X30)|k3_tmap_1(X28,X29,X30,X31,X32)=k2_partfun1(u1_struct_0(X30),u1_struct_0(X29),X32,u1_struct_0(X31)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.43  fof(c_0_43, plain, ![X55, X56, X57]:(~v2_pre_topc(X55)|~l1_pre_topc(X55)|(~m1_pre_topc(X56,X55)|(~m1_pre_topc(X57,X56)|m1_pre_topc(X57,X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.43  fof(c_0_44, plain, ![X24, X25, X26, X27]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))|(~m1_pre_topc(X27,X24)|k2_tmap_1(X24,X25,X26,X27)=k2_partfun1(u1_struct_0(X24),u1_struct_0(X25),X26,u1_struct_0(X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.43  cnf(c_0_45, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_36]), c_0_40])])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_31]), c_0_32])])).
% 0.20/0.43  cnf(c_0_48, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_49, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.43  cnf(c_0_50, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23]), c_0_24]), c_0_25])])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_54, plain, ![X41]:(~l1_pre_topc(X41)|m1_pre_topc(X41,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.43  fof(c_0_55, plain, ![X14, X15, X16, X17]:((~r2_funct_2(X14,X15,X16,X17)|X16=X17|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))&(X16!=X17|r2_funct_2(X14,X15,X16,X17)|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_36])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_36]), c_0_24])])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_30]), c_0_31]), c_0_32])])).
% 0.20/0.43  fof(c_0_59, plain, ![X51, X52, X53, X54]:(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52)|(v2_struct_0(X53)|~m1_pre_topc(X53,X51)|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X53),u1_struct_0(X52))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X52))))|r2_funct_2(u1_struct_0(X53),u1_struct_0(X52),X54,k3_tmap_1(X51,X52,X53,X53,X54)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).
% 0.20/0.43  cnf(c_0_60, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_30]), c_0_24]), c_0_40]), c_0_25]), c_0_52]), c_0_31]), c_0_32])]), c_0_26]), c_0_53])).
% 0.20/0.43  cnf(c_0_62, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.43  cnf(c_0_63, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_56, c_0_40])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_36]), c_0_40])])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_36]), c_0_24])])).
% 0.20/0.43  cnf(c_0_67, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0))=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_30]), c_0_24]), c_0_25]), c_0_31]), c_0_32])]), c_0_26])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_40])])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (X1=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_65, c_0_36])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_36]), c_0_40])])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_30]), c_0_24]), c_0_25]), c_0_31]), c_0_32])]), c_0_53]), c_0_26])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_62]), c_0_69]), c_0_40])])).
% 0.20/0.43  fof(c_0_75, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_pre_topc(X40,X39)|m1_subset_1(u1_struct_0(X40),k1_zfmisc_1(u1_struct_0(X39))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.43  fof(c_0_76, plain, ![X45, X46, X47, X48, X49]:((m1_subset_1(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X46))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&((r2_hidden(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X47))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(k3_funct_2(u1_struct_0(X46),u1_struct_0(X45),X48,esk1_5(X45,X46,X47,X48,X49))!=k1_funct_1(X49,esk1_5(X45,X46,X47,X48,X49))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).
% 0.20/0.43  cnf(c_0_77, negated_conjecture, (X1=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_40])])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_72, c_0_36])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_62]), c_0_40]), c_0_52])]), c_0_53])).
% 0.20/0.43  cnf(c_0_80, negated_conjecture, (k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_62]), c_0_40]), c_0_52])]), c_0_53])).
% 0.20/0.43  cnf(c_0_81, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.43  fof(c_0_82, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|m1_subset_1(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.43  cnf(c_0_83, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X3))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.43  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_85, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_86, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_87, negated_conjecture, (X1=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_40])])).
% 0.20/0.43  cnf(c_0_88, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0))), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.43  cnf(c_0_89, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_81, c_0_62])).
% 0.20/0.43  cnf(c_0_90, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.43  cnf(c_0_91, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_23]), c_0_24])])).
% 0.20/0.43  cnf(c_0_92, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)|r2_hidden(esk1_5(esk2_0,X1,esk3_0,X2,esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_24]), c_0_25]), c_0_85]), c_0_86])]), c_0_53]), c_0_26])).
% 0.20/0.43  cnf(c_0_93, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)=k4_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_31]), c_0_32]), c_0_30])])).
% 0.20/0.43  cnf(c_0_94, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_95, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_89, c_0_40])).
% 0.20/0.43  cnf(c_0_96, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.43  cnf(c_0_97, negated_conjecture, (r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_30]), c_0_93]), c_0_40]), c_0_52]), c_0_31]), c_0_32])]), c_0_53]), c_0_94])).
% 0.20/0.43  fof(c_0_98, plain, ![X10, X11, X12, X13]:(v1_xboole_0(X10)|~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~m1_subset_1(X13,X10)|k3_funct_2(X10,X11,X12,X13)=k1_funct_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.20/0.43  cnf(c_0_99, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_90, c_0_95])).
% 0.20/0.43  fof(c_0_100, plain, ![X58, X59, X60]:(v2_struct_0(X58)|~v2_pre_topc(X58)|~l1_pre_topc(X58)|(v2_struct_0(X59)|~m1_pre_topc(X59,X58)|(~m1_subset_1(X60,u1_struct_0(X58))|(~r2_hidden(X60,u1_struct_0(X59))|k1_funct_1(k4_tmap_1(X58,X59),X60)=X60)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.20/0.43  cnf(c_0_101, negated_conjecture, (m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.20/0.43  cnf(c_0_102, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.20/0.43  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_99, c_0_97])).
% 0.20/0.43  cnf(c_0_104, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.43  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_62]), c_0_40])])).
% 0.20/0.43  fof(c_0_106, plain, ![X23]:(v2_struct_0(X23)|~l1_struct_0(X23)|~v1_xboole_0(u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.43  cnf(c_0_107, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_30]), c_0_32])]), c_0_31])])).
% 0.20/0.43  cnf(c_0_108, negated_conjecture, (m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_62]), c_0_40])])).
% 0.20/0.43  cnf(c_0_109, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,X1),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.43  cnf(c_0_110, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.20/0.43  cnf(c_0_111, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.20/0.43  cnf(c_0_112, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_97]), c_0_23])]), c_0_53])).
% 0.20/0.43  cnf(c_0_113, negated_conjecture, (X1=k1_funct_1(esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_114, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_53])).
% 0.20/0.43  cnf(c_0_115, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_62]), c_0_40])])).
% 0.20/0.43  cnf(c_0_116, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)|~r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_113, c_0_105])).
% 0.20/0.43  cnf(c_0_117, plain, (r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X2,X1,X4,X3,X5))!=k1_funct_1(X5,esk1_5(X2,X1,X4,X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.43  cnf(c_0_118, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)|~l1_struct_0(esk3_0)), inference(rw,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.43  cnf(c_0_119, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_116, c_0_97])).
% 0.20/0.43  cnf(c_0_120, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)|k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0))!=k1_funct_1(esk4_0,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_84]), c_0_24]), c_0_25]), c_0_85]), c_0_86])]), c_0_53]), c_0_26])).
% 0.20/0.43  cnf(c_0_121, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_36]), c_0_40])])).
% 0.20/0.43  cnf(c_0_122, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_62]), c_0_40])])).
% 0.20/0.43  cnf(c_0_123, negated_conjecture, (~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_30]), c_0_93]), c_0_121]), c_0_122]), c_0_40]), c_0_52]), c_0_31]), c_0_32])]), c_0_53]), c_0_94])).
% 0.20/0.43  cnf(c_0_124, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_62]), c_0_40])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 125
% 0.20/0.43  # Proof object clause steps            : 88
% 0.20/0.43  # Proof object formula steps           : 37
% 0.20/0.43  # Proof object conjectures             : 67
% 0.20/0.43  # Proof object clause conjectures      : 64
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 32
% 0.20/0.43  # Proof object initial formulas used   : 18
% 0.20/0.43  # Proof object generating inferences   : 53
% 0.20/0.43  # Proof object simplifying inferences  : 142
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 19
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 36
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 36
% 0.20/0.43  # Processed clauses                    : 472
% 0.20/0.43  # ...of these trivial                  : 3
% 0.20/0.43  # ...subsumed                          : 17
% 0.20/0.43  # ...remaining for further processing  : 452
% 0.20/0.43  # Other redundant clauses eliminated   : 1
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 83
% 0.20/0.43  # Backward-rewritten                   : 46
% 0.20/0.43  # Generated clauses                    : 705
% 0.20/0.43  # ...of the previous two non-trivial   : 722
% 0.20/0.43  # Contextual simplify-reflections      : 51
% 0.20/0.43  # Paramodulations                      : 704
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 1
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 286
% 0.20/0.43  #    Positive orientable unit clauses  : 73
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 4
% 0.20/0.43  #    Non-unit-clauses                  : 209
% 0.20/0.43  # Current number of unprocessed clauses: 317
% 0.20/0.43  # ...number of literals in the above   : 2121
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 165
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 12805
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 3567
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 149
% 0.20/0.43  # Unit Clause-clause subsumption calls : 629
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 277
% 0.20/0.43  # BW rewrite match successes           : 15
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 48057
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.093 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.099 s
% 0.20/0.43  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------

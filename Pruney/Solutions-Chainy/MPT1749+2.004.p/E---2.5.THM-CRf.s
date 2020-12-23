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
% DateTime   : Thu Dec  3 11:17:15 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 616 expanded)
%              Number of clauses        :   59 ( 218 expanded)
%              Number of leaves         :   15 ( 153 expanded)
%              Depth                    :   17
%              Number of atoms          :  387 (6050 expanded)
%              Number of equality atoms :   27 ( 306 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   25 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tmap_1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t59_tmap_1])).

fof(c_0_16,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_pre_topc(X35,X34)
      | l1_pre_topc(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,negated_conjecture,(
    ! [X52] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X52,u1_struct_0(esk3_0))
        | ~ r2_hidden(X52,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X52) = k1_funct_1(esk6_0,X52) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_18,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r2_funct_2(X19,X20,X21,X22)
        | ~ m1_subset_1(X23,X19)
        | k1_funct_1(X21,X23) = k1_funct_1(X22,X23)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(esk1_4(X19,X20,X21,X22),X19)
        | r2_funct_2(X19,X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( k1_funct_1(X21,esk1_4(X19,X20,X21,X22)) != k1_funct_1(X22,esk1_4(X19,X20,X21,X22))
        | r2_funct_2(X19,X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

fof(c_0_19,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | l1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X41,X42,X43,X44] :
      ( ( v1_funct_1(k2_tmap_1(X41,X42,X43,X44))
        | ~ l1_struct_0(X41)
        | ~ l1_struct_0(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
        | ~ l1_struct_0(X44) )
      & ( v1_funct_2(k2_tmap_1(X41,X42,X43,X44),u1_struct_0(X44),u1_struct_0(X42))
        | ~ l1_struct_0(X41)
        | ~ l1_struct_0(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
        | ~ l1_struct_0(X44) )
      & ( m1_subset_1(k2_tmap_1(X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X42))))
        | ~ l1_struct_0(X41)
        | ~ l1_struct_0(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
        | ~ l1_struct_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,plain,(
    ! [X37,X38,X39,X40] :
      ( v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
      | ~ m1_pre_topc(X40,X37)
      | k2_tmap_1(X37,X38,X39,X40) = k2_partfun1(u1_struct_0(X37),u1_struct_0(X38),X39,u1_struct_0(X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0),u1_struct_0(esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

fof(c_0_36,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ v1_funct_1(X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_partfun1(X25,X26,X27,X28) = k7_relat_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_37,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_45,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_46,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_47,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(k2_tmap_1(X1,esk2_0,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_48,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_49,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | m1_subset_1(u1_struct_0(X46),k1_zfmisc_1(u1_struct_0(X45))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_50,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r2_hidden(X16,X17)
      | k1_funct_1(k7_relat_1(X18,X17),X16) = k1_funct_1(X18,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_51,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_30]),c_0_22]),c_0_41]),c_0_42])]),c_0_43]),c_0_44])).

cnf(c_0_53,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_55,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X7,X8)
      | v1_xboole_0(X8)
      | r2_hidden(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34]),c_0_35])])).

cnf(c_0_57,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_59,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_60,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42]),c_0_38])])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_38]),c_0_54])])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_57]),c_0_41]),c_0_42])]),c_0_58])).

fof(c_0_66,plain,(
    ! [X29,X30,X31,X32] :
      ( v1_xboole_0(X29)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,X29,X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ m1_subset_1(X32,X29)
      | k3_funct_2(X29,X30,X31,X32) = k1_funct_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_22])])).

cnf(c_0_69,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1),X2) = k1_funct_1(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_42]),c_0_63])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r2_funct_2(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4)
    | k1_funct_1(esk5_0,esk1_4(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4)) != k1_funct_1(X4,esk1_4(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4))
    | ~ m1_pre_topc(X3,esk3_0)
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X1,X2)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X3))
    | ~ v1_funct_1(X4)
    | ~ r2_hidden(esk1_4(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4),u1_struct_0(X3))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_34]),c_0_35]),c_0_57]),c_0_41]),c_0_42]),c_0_38])])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_funct_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_41]),c_0_42]),c_0_38])]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0)) != k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_21]),c_0_25]),c_0_26]),c_0_24])]),c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0)) = k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_72]),c_0_34]),c_0_35]),c_0_57]),c_0_41]),c_0_42]),c_0_38])])).

fof(c_0_83,plain,(
    ! [X36] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | ~ v1_xboole_0(u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_48]),c_0_34]),c_0_35]),c_0_57]),c_0_41]),c_0_42]),c_0_38])])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_33]),c_0_34]),c_0_35]),c_0_57]),c_0_41]),c_0_42]),c_0_38])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_34])]),c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_88]),c_0_57])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.21/0.50  # and selection function PSelectComplexExceptRRHorn.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.037 s
% 0.21/0.50  # Presaturation interreduction done
% 0.21/0.50  
% 0.21/0.50  # Proof found!
% 0.21/0.50  # SZS status Theorem
% 0.21/0.50  # SZS output start CNFRefutation
% 0.21/0.50  fof(t59_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.21/0.50  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.50  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 0.21/0.50  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.50  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.21/0.50  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.21/0.50  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.21/0.50  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.50  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.50  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.50  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 0.21/0.50  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.50  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.50  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.21/0.50  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.50  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t59_tmap_1])).
% 0.21/0.50  fof(c_0_16, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_pre_topc(X35,X34)|l1_pre_topc(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.50  fof(c_0_17, negated_conjecture, ![X52]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X52,u1_struct_0(esk3_0))|(~r2_hidden(X52,u1_struct_0(esk4_0))|k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X52)=k1_funct_1(esk6_0,X52)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).
% 0.21/0.50  fof(c_0_18, plain, ![X19, X20, X21, X22, X23]:((~r2_funct_2(X19,X20,X21,X22)|(~m1_subset_1(X23,X19)|k1_funct_1(X21,X23)=k1_funct_1(X22,X23))|(~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((m1_subset_1(esk1_4(X19,X20,X21,X22),X19)|r2_funct_2(X19,X20,X21,X22)|(~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&(k1_funct_1(X21,esk1_4(X19,X20,X21,X22))!=k1_funct_1(X22,esk1_4(X19,X20,X21,X22))|r2_funct_2(X19,X20,X21,X22)|(~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.21/0.50  fof(c_0_19, plain, ![X33]:(~l1_pre_topc(X33)|l1_struct_0(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.50  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.50  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_23, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.50  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  fof(c_0_27, plain, ![X41, X42, X43, X44]:(((v1_funct_1(k2_tmap_1(X41,X42,X43,X44))|(~l1_struct_0(X41)|~l1_struct_0(X42)|~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))|~l1_struct_0(X44)))&(v1_funct_2(k2_tmap_1(X41,X42,X43,X44),u1_struct_0(X44),u1_struct_0(X42))|(~l1_struct_0(X41)|~l1_struct_0(X42)|~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))|~l1_struct_0(X44))))&(m1_subset_1(k2_tmap_1(X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X42))))|(~l1_struct_0(X41)|~l1_struct_0(X42)|~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))|~l1_struct_0(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.21/0.50  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.50  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.21/0.50  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  fof(c_0_31, plain, ![X37, X38, X39, X40]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))|(~m1_pre_topc(X40,X37)|k2_tmap_1(X37,X38,X39,X40)=k2_partfun1(u1_struct_0(X37),u1_struct_0(X38),X39,u1_struct_0(X40)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.21/0.50  cnf(c_0_32, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0),u1_struct_0(esk4_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])])).
% 0.21/0.50  cnf(c_0_33, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.50  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.50  cnf(c_0_35, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.21/0.50  fof(c_0_36, plain, ![X25, X26, X27, X28]:(~v1_funct_1(X27)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k2_partfun1(X25,X26,X27,X28)=k7_relat_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.21/0.50  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.50  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  fof(c_0_45, plain, ![X12, X13]:(~v1_relat_1(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_relat_1(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.50  fof(c_0_46, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.50  cnf(c_0_47, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(k2_tmap_1(X1,esk2_0,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.21/0.50  cnf(c_0_48, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.50  fof(c_0_49, plain, ![X45, X46]:(~l1_pre_topc(X45)|(~m1_pre_topc(X46,X45)|m1_subset_1(u1_struct_0(X46),k1_zfmisc_1(u1_struct_0(X45))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.50  fof(c_0_50, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r2_hidden(X16,X17)|k1_funct_1(k7_relat_1(X18,X17),X16)=k1_funct_1(X18,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 0.21/0.50  cnf(c_0_51, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.50  cnf(c_0_52, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_30]), c_0_22]), c_0_41]), c_0_42])]), c_0_43]), c_0_44])).
% 0.21/0.50  cnf(c_0_53, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.50  cnf(c_0_54, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.50  fof(c_0_55, plain, ![X7, X8]:(~m1_subset_1(X7,X8)|(v1_xboole_0(X8)|r2_hidden(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.50  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_34]), c_0_35])])).
% 0.21/0.50  cnf(c_0_57, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.21/0.50  cnf(c_0_58, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  fof(c_0_59, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.50  cnf(c_0_60, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.50  cnf(c_0_61, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.50  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk5_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_42]), c_0_38])])).
% 0.21/0.50  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_38]), c_0_54])])).
% 0.21/0.50  cnf(c_0_64, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.50  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_57]), c_0_41]), c_0_42])]), c_0_58])).
% 0.21/0.50  fof(c_0_66, plain, ![X29, X30, X31, X32]:(v1_xboole_0(X29)|~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,X29)|k3_funct_2(X29,X30,X31,X32)=k1_funct_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.21/0.50  cnf(c_0_67, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.50  cnf(c_0_68, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_21]), c_0_22])])).
% 0.21/0.50  cnf(c_0_69, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.50  cnf(c_0_70, negated_conjecture, (k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1),X2)=k1_funct_1(esk5_0,X2)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_42]), c_0_63])])).
% 0.21/0.50  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.50  cnf(c_0_72, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.50  cnf(c_0_73, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.50  cnf(c_0_74, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1)=k1_funct_1(esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_75, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.50  cnf(c_0_76, negated_conjecture, (r2_funct_2(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4)|k1_funct_1(esk5_0,esk1_4(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4))!=k1_funct_1(X4,esk1_4(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4))|~m1_pre_topc(X3,esk3_0)|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X1,X2)|~v1_funct_2(X4,X1,X2)|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X3))|~v1_funct_1(X4)|~r2_hidden(esk1_4(X1,X2,k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),X4),u1_struct_0(X3))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.50  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_34]), c_0_35]), c_0_57]), c_0_41]), c_0_42]), c_0_38])])).
% 0.21/0.50  cnf(c_0_78, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_funct_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_41]), c_0_42]), c_0_38])]), c_0_75])).
% 0.21/0.50  cnf(c_0_79, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))!=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_21]), c_0_25]), c_0_26]), c_0_24])]), c_0_58])).
% 0.21/0.50  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_78, c_0_77])).
% 0.21/0.50  cnf(c_0_81, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.21/0.50  cnf(c_0_82, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_72]), c_0_34]), c_0_35]), c_0_57]), c_0_41]), c_0_42]), c_0_38])])).
% 0.21/0.50  fof(c_0_83, plain, ![X36]:(v2_struct_0(X36)|~l1_struct_0(X36)|~v1_xboole_0(u1_struct_0(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.50  cnf(c_0_84, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_48]), c_0_34]), c_0_35]), c_0_57]), c_0_41]), c_0_42]), c_0_38])])).
% 0.21/0.50  cnf(c_0_85, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.50  cnf(c_0_86, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_33]), c_0_34]), c_0_35]), c_0_57]), c_0_41]), c_0_42]), c_0_38])])).
% 0.21/0.50  cnf(c_0_87, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.50  cnf(c_0_88, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_34])]), c_0_87])).
% 0.21/0.50  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_88]), c_0_57])]), c_0_44]), ['proof']).
% 0.21/0.50  # SZS output end CNFRefutation
% 0.21/0.50  # Proof object total steps             : 90
% 0.21/0.50  # Proof object clause steps            : 59
% 0.21/0.50  # Proof object formula steps           : 31
% 0.21/0.50  # Proof object conjectures             : 45
% 0.21/0.50  # Proof object clause conjectures      : 42
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 33
% 0.21/0.50  # Proof object initial formulas used   : 15
% 0.21/0.50  # Proof object generating inferences   : 26
% 0.21/0.50  # Proof object simplifying inferences  : 80
% 0.21/0.50  # Training examples: 0 positive, 0 negative
% 0.21/0.50  # Parsed axioms                        : 15
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 34
% 0.21/0.50  # Removed in clause preprocessing      : 0
% 0.21/0.50  # Initial clauses in saturation        : 34
% 0.21/0.50  # Processed clauses                    : 348
% 0.21/0.50  # ...of these trivial                  : 0
% 0.21/0.50  # ...subsumed                          : 74
% 0.21/0.50  # ...remaining for further processing  : 274
% 0.21/0.50  # Other redundant clauses eliminated   : 0
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 43
% 0.21/0.50  # Backward-rewritten                   : 16
% 0.21/0.50  # Generated clauses                    : 848
% 0.21/0.50  # ...of the previous two non-trivial   : 847
% 0.21/0.50  # Contextual simplify-reflections      : 21
% 0.21/0.50  # Paramodulations                      : 841
% 0.21/0.50  # Factorizations                       : 0
% 0.21/0.50  # Equation resolutions                 : 7
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 181
% 0.21/0.50  #    Positive orientable unit clauses  : 22
% 0.21/0.50  #    Positive unorientable unit clauses: 0
% 0.21/0.50  #    Negative unit clauses             : 4
% 0.21/0.50  #    Non-unit-clauses                  : 155
% 0.21/0.50  # Current number of unprocessed clauses: 561
% 0.21/0.50  # ...number of literals in the above   : 8917
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 93
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 16117
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 1710
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 134
% 0.21/0.50  # Unit Clause-clause subsumption calls : 63
% 0.21/0.50  # Rewrite failures with RHS unbound    : 0
% 0.21/0.50  # BW rewrite match attempts            : 4
% 0.21/0.50  # BW rewrite match successes           : 1
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 80048
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.154 s
% 0.21/0.50  # System time              : 0.009 s
% 0.21/0.50  # Total time               : 0.163 s
% 0.21/0.50  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

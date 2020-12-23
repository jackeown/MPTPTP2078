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
% DateTime   : Thu Dec  3 11:17:31 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 369 expanded)
%              Number of clauses        :   57 ( 125 expanded)
%              Number of leaves         :   13 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  401 (4064 expanded)
%              Number of equality atoms :   22 ( 231 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_tmap_1,conjecture,(
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
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X2)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( X5 = X6
                           => ( r1_tmap_1(X2,X1,X3,X5)
                            <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(t65_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( r1_tarski(X5,u1_struct_0(X4))
                                  & m1_connsp_2(X5,X2,X6)
                                  & X6 = X7 )
                               => ( r1_tmap_1(X2,X1,X3,X6)
                                <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(t64_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_tsep_1(X4,X2)
                      & m1_pre_topc(X4,X2) )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ( X5 = X6
                             => ( r1_tmap_1(X2,X1,X3,X5)
                              <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_tmap_1])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    & ~ v2_struct_0(esk4_0)
    & v1_tsep_1(esk4_0,esk2_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & esk5_0 = esk6_0
    & ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)
      | ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0) )
    & ( r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)
      | r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47] :
      ( ( ~ r1_tmap_1(X42,X41,X43,X46)
        | r1_tmap_1(X44,X41,k2_tmap_1(X42,X41,X43,X44),X47)
        | ~ r1_tarski(X45,u1_struct_0(X44))
        | ~ m1_connsp_2(X45,X42,X46)
        | X46 != X47
        | ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X44)
        | ~ m1_pre_topc(X44,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X41))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( ~ r1_tmap_1(X44,X41,k2_tmap_1(X42,X41,X43,X44),X47)
        | r1_tmap_1(X42,X41,X43,X46)
        | ~ r1_tarski(X45,u1_struct_0(X44))
        | ~ m1_connsp_2(X45,X42,X46)
        | X46 != X47
        | ~ m1_subset_1(X47,u1_struct_0(X44))
        | ~ m1_subset_1(X46,u1_struct_0(X42))
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))
        | v2_struct_0(X44)
        | ~ m1_pre_topc(X44,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X41))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)
    | r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)
    | ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X35))
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X36)
      | ~ m1_subset_1(X39,u1_struct_0(X36))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | X39 != X40
      | ~ r1_tmap_1(X36,X35,X37,X39)
      | r1_tmap_1(X38,X35,k2_tmap_1(X36,X35,X37,X38),X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_20,plain,
    ( r1_tmap_1(X3,X2,X4,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | ~ r1_tarski(X7,u1_struct_0(X1))
    | ~ m1_connsp_2(X7,X3,X6)
    | X6 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)
    | r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)
    | esk6_0 != X1
    | ~ m1_connsp_2(X2,esk2_0,X1)
    | ~ r1_tarski(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_17])).

fof(c_0_39,plain,(
    ! [X9] : m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_40,plain,(
    ! [X8] : k2_subset_1(X8) = X8 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_41,negated_conjecture,
    ( X1 != esk6_0
    | ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35,c_0_36]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_33]),c_0_31]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | ~ m1_connsp_2(X1,esk2_0,esk6_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_37]),c_0_38])])).

fof(c_0_43,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | ~ m1_connsp_2(X1,esk2_0,esk6_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_42]),c_0_38])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_50,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X33)
      | m1_subset_1(u1_struct_0(X34),k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | ~ m1_connsp_2(X1,esk2_0,esk6_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(pm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | ~ m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(pm,[status(thm)],[c_0_48,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | ~ m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54,c_0_55]),c_0_26]),c_0_27])])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)
    | ~ m1_connsp_2(X1,esk2_0,esk6_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(pm,[status(thm)],[c_0_56,c_0_42])).

fof(c_0_58,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v1_tsep_1(X31,X30)
        | ~ m1_pre_topc(X31,X30)
        | v3_pre_topc(X32,X30)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v1_tsep_1(X31,X30)
        | ~ v3_pre_topc(X32,X30)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_pre_topc(X31,X30)
        | ~ v3_pre_topc(X32,X30)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_pre_topc(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)
    | ~ m1_connsp_2(X1,esk2_0,esk6_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_57,c_0_47])).

fof(c_0_60,plain,(
    ! [X27,X28,X29] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | ~ v3_pre_topc(X28,X27)
      | ~ r2_hidden(X29,X28)
      | m1_connsp_2(X28,X27,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

cnf(c_0_61,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_59,c_0_52])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_55]),c_0_26]),c_0_27])])).

cnf(c_0_66,plain,
    ( m1_connsp_2(u1_struct_0(X1),X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(pm,[status(thm)],[c_0_63,c_0_53])).

cnf(c_0_67,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_64])).

fof(c_0_68,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_69,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,X11)
      | v1_xboole_0(X11)
      | r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk4_0),esk2_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65,c_0_66]),c_0_24]),c_0_26]),c_0_27]),c_0_38])]),c_0_31])).

cnf(c_0_71,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(pm,[status(thm)],[c_0_67,c_0_53])).

cnf(c_0_72,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_75,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_24]),c_0_26]),c_0_27])])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_78,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_79,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_77]),c_0_30])]),c_0_33])).

cnf(c_0_81,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79,c_0_26]),c_0_27])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80,c_0_81]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.74/0.92  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.74/0.92  # and selection function NoSelection.
% 0.74/0.92  #
% 0.74/0.92  # Preprocessing time       : 0.049 s
% 0.74/0.92  
% 0.74/0.92  # Proof found!
% 0.74/0.92  # SZS status Theorem
% 0.74/0.92  # SZS output start CNFRefutation
% 0.74/0.92  fof(t67_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.74/0.92  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.74/0.92  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.74/0.92  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.74/0.92  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.74/0.92  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.74/0.92  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.74/0.92  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.74/0.92  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.74/0.92  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.74/0.92  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.74/0.92  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.74/0.92  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.74/0.92  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))))), inference(assume_negation,[status(cth)],[t67_tmap_1])).
% 0.74/0.92  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(((~v2_struct_0(esk4_0)&v1_tsep_1(esk4_0,esk2_0))&m1_pre_topc(esk4_0,esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(esk5_0=esk6_0&((~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)|~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0))&(r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)|r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.74/0.92  fof(c_0_15, plain, ![X41, X42, X43, X44, X45, X46, X47]:((~r1_tmap_1(X42,X41,X43,X46)|r1_tmap_1(X44,X41,k2_tmap_1(X42,X41,X43,X44),X47)|(~r1_tarski(X45,u1_struct_0(X44))|~m1_connsp_2(X45,X42,X46)|X46!=X47)|~m1_subset_1(X47,u1_struct_0(X44))|~m1_subset_1(X46,u1_struct_0(X42))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))|(v2_struct_0(X44)|~m1_pre_topc(X44,X42))|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X41))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41)))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(~r1_tmap_1(X44,X41,k2_tmap_1(X42,X41,X43,X44),X47)|r1_tmap_1(X42,X41,X43,X46)|(~r1_tarski(X45,u1_struct_0(X44))|~m1_connsp_2(X45,X42,X46)|X46!=X47)|~m1_subset_1(X47,u1_struct_0(X44))|~m1_subset_1(X46,u1_struct_0(X42))|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))|(v2_struct_0(X44)|~m1_pre_topc(X44,X42))|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X41))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41)))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.74/0.92  cnf(c_0_16, negated_conjecture, (r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)|r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_17, negated_conjecture, (esk5_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_18, negated_conjecture, (~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk5_0)|~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  fof(c_0_19, plain, ![X35, X36, X37, X38, X39, X40]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))|(v2_struct_0(X38)|~m1_pre_topc(X38,X36)|(~m1_subset_1(X39,u1_struct_0(X36))|(~m1_subset_1(X40,u1_struct_0(X38))|(X39!=X40|~r1_tmap_1(X36,X35,X37,X39)|r1_tmap_1(X38,X35,k2_tmap_1(X36,X35,X37,X38),X40)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.74/0.92  cnf(c_0_20, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.74/0.92  cnf(c_0_21, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)|r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.74/0.92  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_35, negated_conjecture, (~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.74/0.92  cnf(c_0_36, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.74/0.92  cnf(c_0_37, negated_conjecture, (r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)|esk6_0!=X1|~m1_connsp_2(X2,esk2_0,X1)|~r1_tarski(X2,u1_struct_0(esk4_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31]), c_0_32]), c_0_33])).
% 0.74/0.92  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_34, c_0_17])).
% 0.74/0.92  fof(c_0_39, plain, ![X9]:m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.74/0.92  fof(c_0_40, plain, ![X8]:k2_subset_1(X8)=X8, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.74/0.92  cnf(c_0_41, negated_conjecture, (X1!=esk6_0|~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35, c_0_36]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_33]), c_0_31]), c_0_32])).
% 0.74/0.92  cnf(c_0_42, negated_conjecture, (r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~m1_connsp_2(X1,esk2_0,esk6_0)|~r1_tarski(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_37]), c_0_38])])).
% 0.74/0.92  fof(c_0_43, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.74/0.92  cnf(c_0_44, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.74/0.92  cnf(c_0_45, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.74/0.92  cnf(c_0_46, negated_conjecture, (~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~m1_connsp_2(X1,esk2_0,esk6_0)|~r1_tarski(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_42]), c_0_38])])).
% 0.74/0.92  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.74/0.92  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.74/0.92  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.74/0.92  fof(c_0_50, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_pre_topc(X34,X33)|m1_subset_1(u1_struct_0(X34),k1_zfmisc_1(u1_struct_0(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.74/0.92  cnf(c_0_51, negated_conjecture, (~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~m1_connsp_2(X1,esk2_0,esk6_0)|~r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(pm,[status(thm)],[c_0_46, c_0_47])).
% 0.74/0.92  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(pm,[status(thm)],[c_0_48, c_0_49])).
% 0.74/0.92  cnf(c_0_53, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.74/0.92  cnf(c_0_54, negated_conjecture, (~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)|~r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(pm,[status(thm)],[c_0_51, c_0_52])).
% 0.74/0.92  cnf(c_0_55, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(pm,[status(thm)],[c_0_48, c_0_53])).
% 0.74/0.92  cnf(c_0_56, negated_conjecture, (~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54, c_0_55]), c_0_26]), c_0_27])])).
% 0.74/0.92  cnf(c_0_57, negated_conjecture, (~m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)|~m1_connsp_2(X1,esk2_0,esk6_0)|~r1_tarski(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(pm,[status(thm)],[c_0_56, c_0_42])).
% 0.74/0.92  fof(c_0_58, plain, ![X30, X31, X32]:((~v1_tsep_1(X31,X30)|~m1_pre_topc(X31,X30)|v3_pre_topc(X32,X30)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X31,X30)|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))&((v1_tsep_1(X31,X30)|~v3_pre_topc(X32,X30)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X31,X30)|(~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(m1_pre_topc(X31,X30)|~v3_pre_topc(X32,X30)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|~m1_pre_topc(X31,X30)|(~v2_pre_topc(X30)|~l1_pre_topc(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.74/0.92  cnf(c_0_59, negated_conjecture, (~m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)|~m1_connsp_2(X1,esk2_0,esk6_0)|~r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(pm,[status(thm)],[c_0_57, c_0_47])).
% 0.74/0.92  fof(c_0_60, plain, ![X27, X28, X29]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~m1_subset_1(X29,u1_struct_0(X27))|(~v3_pre_topc(X28,X27)|~r2_hidden(X29,X28)|m1_connsp_2(X28,X27,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.74/0.92  cnf(c_0_61, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.74/0.92  cnf(c_0_62, negated_conjecture, (~m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)|~r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(pm,[status(thm)],[c_0_59, c_0_52])).
% 0.74/0.92  cnf(c_0_63, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.74/0.92  cnf(c_0_64, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_61])).
% 0.74/0.92  cnf(c_0_65, negated_conjecture, (~m1_connsp_2(u1_struct_0(esk4_0),esk2_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_55]), c_0_26]), c_0_27])])).
% 0.74/0.92  cnf(c_0_66, plain, (m1_connsp_2(u1_struct_0(X1),X2,X3)|v2_struct_0(X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X3,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X2))), inference(pm,[status(thm)],[c_0_63, c_0_53])).
% 0.74/0.92  cnf(c_0_67, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_64])).
% 0.74/0.92  fof(c_0_68, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.74/0.92  fof(c_0_69, plain, ![X10, X11]:(~m1_subset_1(X10,X11)|(v1_xboole_0(X11)|r2_hidden(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.74/0.92  cnf(c_0_70, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk4_0),esk2_0)|~r2_hidden(esk6_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65, c_0_66]), c_0_24]), c_0_26]), c_0_27]), c_0_38])]), c_0_31])).
% 0.74/0.92  cnf(c_0_71, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(pm,[status(thm)],[c_0_67, c_0_53])).
% 0.74/0.92  cnf(c_0_72, negated_conjecture, (v1_tsep_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.74/0.92  cnf(c_0_73, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.74/0.92  cnf(c_0_74, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.74/0.92  fof(c_0_75, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|l1_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.74/0.92  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk6_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_24]), c_0_26]), c_0_27])])).
% 0.74/0.92  cnf(c_0_77, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_73, c_0_74])).
% 0.74/0.92  fof(c_0_78, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.74/0.92  cnf(c_0_79, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.74/0.92  cnf(c_0_80, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_77]), c_0_30])]), c_0_33])).
% 0.74/0.92  cnf(c_0_81, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.74/0.92  cnf(c_0_82, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79, c_0_26]), c_0_27])])).
% 0.74/0.92  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80, c_0_81]), c_0_82])]), ['proof']).
% 0.74/0.92  # SZS output end CNFRefutation
% 0.74/0.92  # Proof object total steps             : 84
% 0.74/0.92  # Proof object clause steps            : 57
% 0.74/0.92  # Proof object formula steps           : 27
% 0.74/0.92  # Proof object conjectures             : 39
% 0.74/0.92  # Proof object clause conjectures      : 36
% 0.74/0.92  # Proof object formula conjectures     : 3
% 0.74/0.92  # Proof object initial clauses used    : 30
% 0.74/0.92  # Proof object initial formulas used   : 13
% 0.74/0.92  # Proof object generating inferences   : 22
% 0.74/0.92  # Proof object simplifying inferences  : 59
% 0.74/0.92  # Training examples: 0 positive, 0 negative
% 0.74/0.92  # Parsed axioms                        : 16
% 0.74/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.74/0.92  # Initial clauses                      : 36
% 0.74/0.92  # Removed in clause preprocessing      : 2
% 0.74/0.92  # Initial clauses in saturation        : 34
% 0.74/0.92  # Processed clauses                    : 1010
% 0.74/0.92  # ...of these trivial                  : 5
% 0.74/0.92  # ...subsumed                          : 582
% 0.74/0.92  # ...remaining for further processing  : 423
% 0.74/0.92  # Other redundant clauses eliminated   : 0
% 0.74/0.92  # Clauses deleted for lack of memory   : 0
% 0.74/0.92  # Backward-subsumed                    : 48
% 0.74/0.92  # Backward-rewritten                   : 0
% 0.74/0.92  # Generated clauses                    : 27049
% 0.74/0.92  # ...of the previous two non-trivial   : 26919
% 0.74/0.92  # Contextual simplify-reflections      : 0
% 0.74/0.92  # Paramodulations                      : 27005
% 0.74/0.92  # Factorizations                       : 4
% 0.74/0.92  # Equation resolutions                 : 40
% 0.74/0.92  # Propositional unsat checks           : 0
% 0.74/0.92  #    Propositional check models        : 0
% 0.74/0.92  #    Propositional check unsatisfiable : 0
% 0.74/0.92  #    Propositional clauses             : 0
% 0.74/0.92  #    Propositional clauses after purity: 0
% 0.74/0.92  #    Propositional unsat core size     : 0
% 0.74/0.92  #    Propositional preprocessing time  : 0.000
% 0.74/0.92  #    Propositional encoding time       : 0.000
% 0.74/0.92  #    Propositional solver time         : 0.000
% 0.74/0.92  #    Success case prop preproc time    : 0.000
% 0.74/0.92  #    Success case prop encoding time   : 0.000
% 0.74/0.92  #    Success case prop solver time     : 0.000
% 0.74/0.92  # Current number of processed clauses  : 375
% 0.74/0.92  #    Positive orientable unit clauses  : 16
% 0.74/0.92  #    Positive unorientable unit clauses: 0
% 0.74/0.92  #    Negative unit clauses             : 6
% 0.74/0.92  #    Non-unit-clauses                  : 353
% 0.74/0.92  # Current number of unprocessed clauses: 25879
% 0.74/0.92  # ...number of literals in the above   : 231837
% 0.74/0.92  # Current number of archived formulas  : 0
% 0.74/0.92  # Current number of archived clauses   : 49
% 0.74/0.92  # Clause-clause subsumption calls (NU) : 6668
% 0.74/0.92  # Rec. Clause-clause subsumption calls : 2295
% 0.74/0.92  # Non-unit clause-clause subsumptions  : 574
% 0.74/0.92  # Unit Clause-clause subsumption calls : 314
% 0.74/0.92  # Rewrite failures with RHS unbound    : 0
% 0.74/0.92  # BW rewrite match attempts            : 2
% 0.74/0.92  # BW rewrite match successes           : 0
% 0.74/0.92  # Condensation attempts                : 0
% 0.74/0.92  # Condensation successes               : 0
% 0.74/0.92  # Termbank termtop insertions          : 394343
% 0.74/0.92  
% 0.74/0.92  # -------------------------------------------------
% 0.74/0.92  # User time                : 0.563 s
% 0.74/0.92  # System time              : 0.015 s
% 0.74/0.92  # Total time               : 0.578 s
% 0.74/0.92  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

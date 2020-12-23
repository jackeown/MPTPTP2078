%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:43 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  102 (19191 expanded)
%              Number of clauses        :   81 (6622 expanded)
%              Number of leaves         :   10 (4423 expanded)
%              Depth                    :   16
%              Number of atoms          :  380 (288647 expanded)
%              Number of equality atoms :   45 (14433 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ! [X7] :
                              ( ( v1_funct_1(X7)
                                & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( X4 = X1
                                  & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                               => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(c_0_10,negated_conjecture,(
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
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                               => ( ( X4 = X1
                                    & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                                 => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                  <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_tmap_1])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk2_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
    & esk5_0 = esk2_0
    & r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0)
    & ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
      | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) )
    & ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
      | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X34)
      | ~ m1_pre_topc(X37,X34)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
      | ~ m1_pre_topc(X37,X36)
      | k3_tmap_1(X34,X35,X36,X37,X38) = k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),X38,u1_struct_0(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_13,plain,(
    ! [X39,X40,X41] :
      ( ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X39)
      | ~ m1_pre_topc(X41,X40)
      | m1_pre_topc(X41,X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_14,plain,(
    ! [X30,X31,X32,X33] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
      | ~ m1_pre_topc(X33,X30)
      | k2_tmap_1(X30,X31,X32,X33) = k2_partfun1(u1_struct_0(X30),u1_struct_0(X31),X32,u1_struct_0(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( esk5_0 = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_31,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_32,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_33,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
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
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk3_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk2_0,X2,esk8_0) = k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_23]),c_0_25]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r1_funct_2(X24,X25,X26,X27,X28,X29)
        | X28 = X29
        | v1_xboole_0(X25)
        | v1_xboole_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X24,X25)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != X29
        | r1_funct_2(X24,X25,X26,X27,X28,X29)
        | v1_xboole_0(X25)
        | v1_xboole_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X24,X25)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk2_0,esk4_0,esk8_0) = k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_37]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_16])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_55,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X21)))
      | v1_xboole_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0) = k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24]),c_0_26])]),c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_28])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_16])).

cnf(c_0_69,negated_conjecture,
    ( esk8_0 = esk6_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_22]),c_0_59]),c_0_27]),c_0_60]),c_0_28]),c_0_61])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0),esk7_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( esk8_0 = k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0),esk7_0)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0) = k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_69])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( esk7_0 = k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( esk8_0 = k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( esk8_0 = X1
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_61])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_28])).

cnf(c_0_85,negated_conjecture,
    ( esk8_0 = k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_86,negated_conjecture,
    ( esk8_0 = X1
    | ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_73])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_64])).

cnf(c_0_88,negated_conjecture,
    ( esk7_0 = k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_80])])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 = k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_80])]),c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = X1
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_80])]),c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_80])]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 = k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_73])).

cnf(c_0_95,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) = k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( esk6_0 = k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_80])])).

cnf(c_0_98,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),X1)
    | ~ v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_77])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_88]),c_0_88]),c_0_85]),c_0_95]),c_0_96]),c_0_95]),c_0_97]),c_0_95]),c_0_96]),c_0_95])])).

cnf(c_0_100,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,u1_struct_0(esk3_0),esk4_0),X1)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_63]),c_0_85]),c_0_95]),c_0_97]),c_0_95]),c_0_88]),c_0_96]),c_0_95]),c_0_80])])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:04:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.48  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.48  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.48  #
% 0.18/0.48  # Preprocessing time       : 0.029 s
% 0.18/0.48  # Presaturation interreduction done
% 0.18/0.48  
% 0.18/0.48  # Proof found!
% 0.18/0.48  # SZS status Theorem
% 0.18/0.48  # SZS output start CNFRefutation
% 0.18/0.48  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.18/0.48  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.18/0.48  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.18/0.48  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.48  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.18/0.48  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.48  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.18/0.48  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.18/0.48  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.18/0.48  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&((esk5_0=esk2_0&r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0))&((~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0))&(r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.18/0.48  fof(c_0_12, plain, ![X34, X35, X36, X37, X38]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_pre_topc(X36,X34)|(~m1_pre_topc(X37,X34)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))|(~m1_pre_topc(X37,X36)|k3_tmap_1(X34,X35,X36,X37,X38)=k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),X38,u1_struct_0(X37)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.18/0.48  fof(c_0_13, plain, ![X39, X40, X41]:(~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~m1_pre_topc(X40,X39)|(~m1_pre_topc(X41,X40)|m1_pre_topc(X41,X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.18/0.48  fof(c_0_14, plain, ![X30, X31, X32, X33]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))|(~m1_pre_topc(X33,X30)|k2_tmap_1(X30,X31,X32,X33)=k2_partfun1(u1_struct_0(X30),u1_struct_0(X31),X32,u1_struct_0(X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.48  cnf(c_0_15, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_16, negated_conjecture, (esk5_0=esk2_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  fof(c_0_18, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.48  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.48  cnf(c_0_20, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.48  cnf(c_0_21, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.48  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.48  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.18/0.48  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  fof(c_0_31, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|~v1_xboole_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.18/0.48  fof(c_0_32, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.48  fof(c_0_33, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.48  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.48  cnf(c_0_35, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.48  cnf(c_0_36, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X1))=k2_tmap_1(esk2_0,esk3_0,esk8_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.18/0.48  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.48  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.48  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.48  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.18/0.48  cnf(c_0_42, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk2_0,X2,esk8_0)=k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_23]), c_0_25]), c_0_27]), c_0_28])]), c_0_29])).
% 0.18/0.48  cnf(c_0_43, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(esk4_0))=k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.48  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.48  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.48  fof(c_0_47, plain, ![X24, X25, X26, X27, X28, X29]:((~r1_funct_2(X24,X25,X26,X27,X28,X29)|X28=X29|(v1_xboole_0(X25)|v1_xboole_0(X27)|~v1_funct_1(X28)|~v1_funct_2(X28,X24,X25)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~v1_funct_1(X29)|~v1_funct_2(X29,X26,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(X28!=X29|r1_funct_2(X24,X25,X26,X27,X28,X29)|(v1_xboole_0(X25)|v1_xboole_0(X27)|~v1_funct_1(X28)|~v1_funct_2(X28,X24,X25)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~v1_funct_1(X29)|~v1_funct_2(X29,X26,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.18/0.48  cnf(c_0_48, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_49, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_50, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk2_0,esk4_0,esk8_0)=k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_37]), c_0_43])).
% 0.18/0.48  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_44, c_0_16])).
% 0.18/0.48  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.48  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.48  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.48  fof(c_0_55, plain, ![X21, X22, X23]:(~v1_xboole_0(X21)|(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X21)))|v1_xboole_0(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.18/0.48  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_57, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.48  cnf(c_0_58, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_48, c_0_16])).
% 0.18/0.48  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_62, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(rw,[status(thm)],[c_0_49, c_0_16])).
% 0.18/0.48  cnf(c_0_63, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0)=k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_24]), c_0_26])]), c_0_30])).
% 0.18/0.48  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.48  cnf(c_0_65, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.48  cnf(c_0_66, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_54, c_0_28])).
% 0.18/0.48  cnf(c_0_67, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.48  cnf(c_0_68, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(rw,[status(thm)],[c_0_56, c_0_16])).
% 0.18/0.48  cnf(c_0_69, negated_conjecture, (esk8_0=esk6_0|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_22]), c_0_59]), c_0_27]), c_0_60]), c_0_28]), c_0_61])])).
% 0.18/0.48  cnf(c_0_70, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.18/0.48  cnf(c_0_71, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_54, c_0_64])).
% 0.18/0.48  cnf(c_0_72, negated_conjecture, (esk8_0=k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.18/0.48  cnf(c_0_73, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_67, c_0_46])).
% 0.18/0.48  cnf(c_0_74, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.48  cnf(c_0_75, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0)=k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_63, c_0_69])).
% 0.18/0.48  cnf(c_0_76, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_69])).
% 0.18/0.48  cnf(c_0_77, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_65, c_0_53])).
% 0.18/0.48  cnf(c_0_78, negated_conjecture, (esk7_0=k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_65, c_0_71])).
% 0.18/0.48  cnf(c_0_79, negated_conjecture, (esk8_0=k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.18/0.48  cnf(c_0_80, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.18/0.48  cnf(c_0_81, negated_conjecture, (esk8_0=X1|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_72, c_0_77])).
% 0.18/0.48  cnf(c_0_82, negated_conjecture, (esk7_0=k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_78, c_0_73])).
% 0.18/0.48  cnf(c_0_83, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_54, c_0_61])).
% 0.18/0.48  cnf(c_0_84, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_28])).
% 0.18/0.48  cnf(c_0_85, negated_conjecture, (esk8_0=k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.18/0.48  cnf(c_0_86, negated_conjecture, (esk8_0=X1|~v1_xboole_0(u1_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_81, c_0_73])).
% 0.18/0.48  cnf(c_0_87, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_64])).
% 0.18/0.48  cnf(c_0_88, negated_conjecture, (esk7_0=k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_80])])).
% 0.18/0.48  cnf(c_0_89, negated_conjecture, (esk6_0=k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_65, c_0_83])).
% 0.18/0.48  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk3_0)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_77, c_0_80])).
% 0.18/0.48  cnf(c_0_91, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_80])]), c_0_85])).
% 0.18/0.48  cnf(c_0_92, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))=X1|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_80])]), c_0_85])).
% 0.18/0.48  cnf(c_0_93, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_80])]), c_0_88])).
% 0.18/0.48  cnf(c_0_94, negated_conjecture, (esk6_0=k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_89, c_0_73])).
% 0.18/0.48  cnf(c_0_95, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))=u1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.18/0.48  cnf(c_0_96, negated_conjecture, (k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))=k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.18/0.48  cnf(c_0_97, negated_conjecture, (esk6_0=k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_80])])).
% 0.18/0.48  cnf(c_0_98, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),X1)|~v1_xboole_0(esk7_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_77])).
% 0.18/0.48  cnf(c_0_99, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_88]), c_0_88]), c_0_85]), c_0_95]), c_0_96]), c_0_95]), c_0_97]), c_0_95]), c_0_96]), c_0_95])])).
% 0.18/0.48  cnf(c_0_100, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,u1_struct_0(esk3_0),esk4_0),X1)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_63]), c_0_85]), c_0_95]), c_0_97]), c_0_95]), c_0_88]), c_0_96]), c_0_95]), c_0_80])])).
% 0.18/0.48  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_80])]), ['proof']).
% 0.18/0.48  # SZS output end CNFRefutation
% 0.18/0.48  # Proof object total steps             : 102
% 0.18/0.48  # Proof object clause steps            : 81
% 0.18/0.48  # Proof object formula steps           : 21
% 0.18/0.48  # Proof object conjectures             : 65
% 0.18/0.48  # Proof object clause conjectures      : 62
% 0.18/0.48  # Proof object formula conjectures     : 3
% 0.18/0.48  # Proof object initial clauses used    : 30
% 0.18/0.48  # Proof object initial formulas used   : 10
% 0.18/0.48  # Proof object generating inferences   : 34
% 0.18/0.48  # Proof object simplifying inferences  : 75
% 0.18/0.48  # Training examples: 0 positive, 0 negative
% 0.18/0.48  # Parsed axioms                        : 10
% 0.18/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.48  # Initial clauses                      : 38
% 0.18/0.48  # Removed in clause preprocessing      : 0
% 0.18/0.48  # Initial clauses in saturation        : 38
% 0.18/0.48  # Processed clauses                    : 1359
% 0.18/0.48  # ...of these trivial                  : 8
% 0.18/0.48  # ...subsumed                          : 834
% 0.18/0.48  # ...remaining for further processing  : 517
% 0.18/0.48  # Other redundant clauses eliminated   : 3
% 0.18/0.48  # Clauses deleted for lack of memory   : 0
% 0.18/0.48  # Backward-subsumed                    : 5
% 0.18/0.48  # Backward-rewritten                   : 371
% 0.18/0.48  # Generated clauses                    : 4074
% 0.18/0.48  # ...of the previous two non-trivial   : 4273
% 0.18/0.48  # Contextual simplify-reflections      : 5
% 0.18/0.48  # Paramodulations                      : 4071
% 0.18/0.48  # Factorizations                       : 0
% 0.18/0.48  # Equation resolutions                 : 3
% 0.18/0.48  # Propositional unsat checks           : 0
% 0.18/0.48  #    Propositional check models        : 0
% 0.18/0.48  #    Propositional check unsatisfiable : 0
% 0.18/0.48  #    Propositional clauses             : 0
% 0.18/0.48  #    Propositional clauses after purity: 0
% 0.18/0.48  #    Propositional unsat core size     : 0
% 0.18/0.48  #    Propositional preprocessing time  : 0.000
% 0.18/0.48  #    Propositional encoding time       : 0.000
% 0.18/0.48  #    Propositional solver time         : 0.000
% 0.18/0.48  #    Success case prop preproc time    : 0.000
% 0.18/0.48  #    Success case prop encoding time   : 0.000
% 0.18/0.48  #    Success case prop solver time     : 0.000
% 0.18/0.48  # Current number of processed clauses  : 102
% 0.18/0.48  #    Positive orientable unit clauses  : 22
% 0.18/0.48  #    Positive unorientable unit clauses: 0
% 0.18/0.48  #    Negative unit clauses             : 4
% 0.18/0.48  #    Non-unit-clauses                  : 76
% 0.18/0.48  # Current number of unprocessed clauses: 2966
% 0.18/0.48  # ...number of literals in the above   : 13588
% 0.18/0.48  # Current number of archived formulas  : 0
% 0.18/0.48  # Current number of archived clauses   : 412
% 0.18/0.48  # Clause-clause subsumption calls (NU) : 36299
% 0.18/0.48  # Rec. Clause-clause subsumption calls : 11337
% 0.18/0.48  # Non-unit clause-clause subsumptions  : 841
% 0.18/0.48  # Unit Clause-clause subsumption calls : 49
% 0.18/0.48  # Rewrite failures with RHS unbound    : 0
% 0.18/0.48  # BW rewrite match attempts            : 49
% 0.18/0.48  # BW rewrite match successes           : 11
% 0.18/0.48  # Condensation attempts                : 0
% 0.18/0.48  # Condensation successes               : 0
% 0.18/0.48  # Termbank termtop insertions          : 73626
% 0.18/0.48  
% 0.18/0.48  # -------------------------------------------------
% 0.18/0.48  # User time                : 0.137 s
% 0.18/0.48  # System time              : 0.007 s
% 0.18/0.48  # Total time               : 0.144 s
% 0.18/0.48  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

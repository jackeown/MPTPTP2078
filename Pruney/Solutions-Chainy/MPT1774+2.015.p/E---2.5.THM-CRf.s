%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:50 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 558 expanded)
%              Number of clauses        :   62 ( 202 expanded)
%              Number of leaves         :    9 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  529 (7752 expanded)
%              Number of equality atoms :   20 ( 311 expanded)
%              Maximal formula depth    :   33 (   7 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t85_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( v3_pre_topc(X6,X2)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X1,X5,X7)
                                      <=> r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

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

fof(t84_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( v3_pre_topc(X6,X4)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X2,X5,X7)
                                      <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(t9_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( ( v3_pre_topc(X3,X1)
                          & r1_tarski(X3,u1_struct_0(X2))
                          & r1_tarski(X4,X3)
                          & X4 = X5 )
                       => ( v3_pre_topc(X5,X2)
                        <=> v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t81_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( X6 = X7
                                  & m1_pre_topc(X4,X3)
                                  & r1_tmap_1(X3,X2,X5,X6) )
                               => r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

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
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X2) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X3))
                                     => ( ( v3_pre_topc(X6,X2)
                                          & r2_hidden(X7,X6)
                                          & r1_tarski(X6,u1_struct_0(X3))
                                          & X7 = X8 )
                                       => ( r1_tmap_1(X4,X1,X5,X7)
                                        <=> r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_tmap_1])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_tarski(u1_struct_0(X20),u1_struct_0(X21))
        | m1_pre_topc(X20,X21)
        | ~ m1_pre_topc(X21,X19)
        | ~ m1_pre_topc(X20,X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_pre_topc(X20,X21)
        | r1_tarski(u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_pre_topc(X21,X19)
        | ~ m1_pre_topc(X20,X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] :
      ( ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | ~ m1_pre_topc(X24,X23)
      | m1_pre_topc(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    & m1_pre_topc(esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk4_0))
    & v3_pre_topc(esk7_0,esk3_0)
    & r2_hidden(esk8_0,esk7_0)
    & r1_tarski(esk7_0,u1_struct_0(esk4_0))
    & esk8_0 = esk9_0
    & ( ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
      | ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) )
    & ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
      | r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r1_tmap_1(X35,X33,X36,X38)
        | r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X39)
        | ~ v3_pre_topc(X37,X35)
        | ~ r2_hidden(X38,X37)
        | ~ r1_tarski(X37,u1_struct_0(X34))
        | X38 != X39
        | ~ m1_subset_1(X39,u1_struct_0(X34))
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X35),u1_struct_0(X33))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33))))
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X32)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X39)
        | r1_tmap_1(X35,X33,X36,X38)
        | ~ v3_pre_topc(X37,X35)
        | ~ r2_hidden(X38,X37)
        | ~ r1_tarski(X37,u1_struct_0(X34))
        | X38 != X39
        | ~ m1_subset_1(X39,u1_struct_0(X34))
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X35),u1_struct_0(X33))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33))))
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X32)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk4_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ( ~ v3_pre_topc(X44,X41)
        | v3_pre_topc(X43,X40)
        | ~ v3_pre_topc(X42,X40)
        | ~ r1_tarski(X42,u1_struct_0(X41))
        | ~ r1_tarski(X43,X42)
        | X43 != X44
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_pre_topc(X41,X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ v3_pre_topc(X43,X40)
        | v3_pre_topc(X44,X41)
        | ~ v3_pre_topc(X42,X40)
        | ~ r1_tarski(X42,u1_struct_0(X41))
        | ~ r1_tarski(X43,X42)
        | X43 != X44
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_pre_topc(X41,X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_tsep_1])])])])).

cnf(c_0_29,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | ~ v3_pre_topc(X8,X4)
    | ~ r2_hidden(X7,X8)
    | ~ r1_tarski(X8,u1_struct_0(X1))
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),X2)
    | r1_tarski(esk7_0,X1)
    | ~ r1_tarski(u1_struct_0(esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( v3_pre_topc(X3,X4)
    | ~ v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X5,X2)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ r1_tarski(X1,X5)
    | X1 != X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ v3_pre_topc(X7,X1)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ r2_hidden(X4,X7)
    | ~ r1_tarski(X7,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_29,c_0_17])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_42,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk5_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X3,X4)
    | ~ v3_pre_topc(X1,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v3_pre_topc(X4,esk5_0)
    | ~ r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X3,esk6_0),X1)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X3,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(X4,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(esk7_0,u1_struct_0(X2))
    | ~ r1_tarski(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_22]),c_0_23]),c_0_47])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_57,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X25)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
      | ~ m1_subset_1(X30,u1_struct_0(X27))
      | ~ m1_subset_1(X31,u1_struct_0(X28))
      | X30 != X31
      | ~ m1_pre_topc(X28,X27)
      | ~ r1_tmap_1(X27,X26,X29,X30)
      | r1_tmap_1(X28,X26,k3_tmap_1(X25,X26,X27,X28,X29),X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(esk7_0,esk5_0)
    | ~ r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ r1_tarski(esk7_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk7_0,X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_47]),c_0_55])]),c_0_56])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | X6 != X7
    | ~ m1_pre_topc(X4,X3)
    | ~ r1_tmap_1(X3,X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(esk7_0,esk5_0)
    | ~ r1_tmap_1(X2,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,X2,esk6_0),esk8_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X2))
    | ~ r1_tarski(esk7_0,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_21])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,X5,X6)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X4)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_61,c_0_17])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ r1_tarski(esk7_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,X3)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40]),c_0_41])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_21]),c_0_27]),c_0_22]),c_0_23]),c_0_70]),c_0_19])]),c_0_71]),c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_76,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_51])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_70]),c_0_27])]),c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_74])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_21]),c_0_22]),c_0_23])]),c_0_79]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n017.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:08:46 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.11/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.11/0.38  #
% 0.11/0.38  # Preprocessing time       : 0.029 s
% 0.11/0.38  # Presaturation interreduction done
% 0.11/0.38  
% 0.11/0.38  # Proof found!
% 0.11/0.38  # SZS status Theorem
% 0.11/0.38  # SZS output start CNFRefutation
% 0.11/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.11/0.38  fof(t85_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 0.11/0.38  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.11/0.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.11/0.38  fof(t84_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.11/0.38  fof(t9_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>((((v3_pre_topc(X3,X1)&r1_tarski(X3,u1_struct_0(X2)))&r1_tarski(X4,X3))&X4=X5)=>(v3_pre_topc(X5,X2)<=>v3_pre_topc(X4,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tsep_1)).
% 0.11/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.11/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.11/0.38  fof(t81_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((X6=X7&m1_pre_topc(X4,X3))&r1_tmap_1(X3,X2,X5,X6))=>r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 0.11/0.38  fof(c_0_9, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.11/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t85_tmap_1])).
% 0.11/0.38  fof(c_0_11, plain, ![X19, X20, X21]:((~r1_tarski(u1_struct_0(X20),u1_struct_0(X21))|m1_pre_topc(X20,X21)|~m1_pre_topc(X21,X19)|~m1_pre_topc(X20,X19)|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~m1_pre_topc(X20,X21)|r1_tarski(u1_struct_0(X20),u1_struct_0(X21))|~m1_pre_topc(X21,X19)|~m1_pre_topc(X20,X19)|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.11/0.38  fof(c_0_12, plain, ![X22, X23, X24]:(~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|(~m1_pre_topc(X24,X23)|m1_pre_topc(X24,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.11/0.38  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.38  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.38  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk4_0))&((((v3_pre_topc(esk7_0,esk3_0)&r2_hidden(esk8_0,esk7_0))&r1_tarski(esk7_0,u1_struct_0(esk4_0)))&esk8_0=esk9_0)&((~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0))&(r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.11/0.38  cnf(c_0_16, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.38  cnf(c_0_17, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.38  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.11/0.38  cnf(c_0_19, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_20, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.38  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  fof(c_0_24, plain, ![X32, X33, X34, X35, X36, X37, X38, X39]:((~r1_tmap_1(X35,X33,X36,X38)|r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X39)|(~v3_pre_topc(X37,X35)|~r2_hidden(X38,X37)|~r1_tarski(X37,u1_struct_0(X34))|X38!=X39)|~m1_subset_1(X39,u1_struct_0(X34))|~m1_subset_1(X38,u1_struct_0(X35))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X35),u1_struct_0(X33))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X39)|r1_tmap_1(X35,X33,X36,X38)|(~v3_pre_topc(X37,X35)|~r2_hidden(X38,X37)|~r1_tarski(X37,u1_struct_0(X34))|X38!=X39)|~m1_subset_1(X39,u1_struct_0(X34))|~m1_subset_1(X38,u1_struct_0(X35))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X35),u1_struct_0(X33))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).
% 0.11/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk4_0))|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.11/0.38  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  fof(c_0_28, plain, ![X40, X41, X42, X43, X44]:((~v3_pre_topc(X44,X41)|v3_pre_topc(X43,X40)|(~v3_pre_topc(X42,X40)|~r1_tarski(X42,u1_struct_0(X41))|~r1_tarski(X43,X42)|X43!=X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|~m1_pre_topc(X41,X40)|(~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(~v3_pre_topc(X43,X40)|v3_pre_topc(X44,X41)|(~v3_pre_topc(X42,X40)|~r1_tarski(X42,u1_struct_0(X41))|~r1_tarski(X43,X42)|X43!=X44)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|~m1_pre_topc(X41,X40)|(~v2_pre_topc(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_tsep_1])])])])).
% 0.11/0.38  cnf(c_0_29, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~v3_pre_topc(X8,X4)|~r2_hidden(X7,X8)|~r1_tarski(X8,u1_struct_0(X1))|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),X2)|r1_tarski(esk7_0,X1)|~r1_tarski(u1_struct_0(esk4_0),X2)), inference(spm,[status(thm)],[c_0_13, c_0_25])).
% 0.11/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.11/0.38  cnf(c_0_32, plain, (v3_pre_topc(X3,X4)|~v3_pre_topc(X1,X2)|~v3_pre_topc(X5,X2)|~r1_tarski(X5,u1_struct_0(X4))|~r1_tarski(X1,X5)|X1!=X3|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.11/0.38  fof(c_0_33, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.11/0.38  cnf(c_0_34, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~v3_pre_topc(X7,X1)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~r2_hidden(X4,X7)|~r1_tarski(X7,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_29, c_0_17])])).
% 0.11/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  fof(c_0_42, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.11/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk5_0))|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.11/0.38  cnf(c_0_45, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X3,X4)|~v3_pre_topc(X1,X4)|~m1_pre_topc(X2,X4)|~l1_pre_topc(X4)|~v2_pre_topc(X4)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X4)))|~r1_tarski(X3,u1_struct_0(X2))|~r1_tarski(X1,X3)), inference(er,[status(thm)],[c_0_32])).
% 0.11/0.38  cnf(c_0_46, negated_conjecture, (v3_pre_topc(esk7_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.11/0.38  cnf(c_0_49, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v3_pre_topc(X4,esk5_0)|~r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X3,esk6_0),X1)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X3,esk5_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X1,X4)|~r1_tarski(X4,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40]), c_0_41])).
% 0.11/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.11/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.11/0.38  cnf(c_0_54, negated_conjecture, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,esk3_0)|~m1_pre_topc(X2,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(esk7_0,u1_struct_0(X2))|~r1_tarski(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_22]), c_0_23]), c_0_47])])).
% 0.11/0.38  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.11/0.38  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.11/0.38  fof(c_0_57, plain, ![X25, X26, X27, X28, X29, X30, X31]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))|(~m1_subset_1(X30,u1_struct_0(X27))|(~m1_subset_1(X31,u1_struct_0(X28))|(X30!=X31|~m1_pre_topc(X28,X27)|~r1_tmap_1(X27,X26,X29,X30)|r1_tmap_1(X28,X26,k3_tmap_1(X25,X26,X27,X28,X29),X31))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).
% 0.11/0.38  cnf(c_0_58, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~v3_pre_topc(esk7_0,esk5_0)|~r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X1,esk5_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(esk8_0,u1_struct_0(X1))|~r1_tarski(esk7_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.11/0.38  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.11/0.38  cnf(c_0_60, negated_conjecture, (v3_pre_topc(esk7_0,X1)|~m1_pre_topc(X1,esk3_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_46]), c_0_47]), c_0_55])]), c_0_56])).
% 0.11/0.38  cnf(c_0_61, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,u1_struct_0(X4))|X6!=X7|~m1_pre_topc(X4,X3)|~r1_tmap_1(X3,X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.11/0.38  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~v3_pre_topc(esk7_0,esk5_0)|~r1_tmap_1(X2,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,X2,esk6_0),esk8_0)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,esk5_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk8_0,u1_struct_0(X2))|~r1_tarski(esk7_0,u1_struct_0(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.11/0.38  cnf(c_0_63, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_21])])).
% 0.11/0.38  cnf(c_0_64, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_65, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_67, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X4,X2,X5,X6)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X4))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_61, c_0_17])])).
% 0.11/0.38  cnf(c_0_68, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X1,esk5_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk8_0,u1_struct_0(X1))|~r1_tarski(esk7_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.11/0.38  cnf(c_0_69, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.11/0.38  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_66, c_0_65])).
% 0.11/0.38  cnf(c_0_71, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_72, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_73, negated_conjecture, (r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(esk5_0,esk2_0,esk6_0,X3)|~m1_pre_topc(X1,esk5_0)|~m1_pre_topc(esk5_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40]), c_0_41])).
% 0.11/0.38  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_21]), c_0_27]), c_0_22]), c_0_23]), c_0_70]), c_0_19])]), c_0_71]), c_0_72])).
% 0.11/0.38  cnf(c_0_75, negated_conjecture, (~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.38  cnf(c_0_76, negated_conjecture, (r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~m1_pre_topc(esk5_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_51])])).
% 0.11/0.38  cnf(c_0_77, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_75, c_0_65])).
% 0.11/0.38  cnf(c_0_78, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_70]), c_0_27])]), c_0_71])).
% 0.11/0.38  cnf(c_0_79, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_74])])).
% 0.11/0.38  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_21]), c_0_22]), c_0_23])]), c_0_79]), c_0_72]), ['proof']).
% 0.11/0.38  # SZS output end CNFRefutation
% 0.11/0.38  # Proof object total steps             : 81
% 0.11/0.38  # Proof object clause steps            : 62
% 0.11/0.38  # Proof object formula steps           : 19
% 0.11/0.38  # Proof object conjectures             : 48
% 0.11/0.38  # Proof object clause conjectures      : 45
% 0.11/0.38  # Proof object formula conjectures     : 3
% 0.11/0.38  # Proof object initial clauses used    : 33
% 0.11/0.38  # Proof object initial formulas used   : 9
% 0.11/0.38  # Proof object generating inferences   : 18
% 0.11/0.38  # Proof object simplifying inferences  : 64
% 0.11/0.38  # Training examples: 0 positive, 0 negative
% 0.11/0.38  # Parsed axioms                        : 9
% 0.11/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.38  # Initial clauses                      : 39
% 0.11/0.38  # Removed in clause preprocessing      : 0
% 0.11/0.38  # Initial clauses in saturation        : 39
% 0.11/0.38  # Processed clauses                    : 158
% 0.11/0.38  # ...of these trivial                  : 1
% 0.11/0.38  # ...subsumed                          : 11
% 0.11/0.38  # ...remaining for further processing  : 146
% 0.11/0.38  # Other redundant clauses eliminated   : 7
% 0.11/0.38  # Clauses deleted for lack of memory   : 0
% 0.11/0.38  # Backward-subsumed                    : 0
% 0.11/0.38  # Backward-rewritten                   : 8
% 0.11/0.38  # Generated clauses                    : 116
% 0.11/0.38  # ...of the previous two non-trivial   : 88
% 0.11/0.38  # Contextual simplify-reflections      : 5
% 0.11/0.38  # Paramodulations                      : 109
% 0.11/0.38  # Factorizations                       : 0
% 0.11/0.38  # Equation resolutions                 : 7
% 0.11/0.38  # Propositional unsat checks           : 0
% 0.11/0.38  #    Propositional check models        : 0
% 0.11/0.38  #    Propositional check unsatisfiable : 0
% 0.11/0.38  #    Propositional clauses             : 0
% 0.11/0.38  #    Propositional clauses after purity: 0
% 0.11/0.38  #    Propositional unsat core size     : 0
% 0.11/0.38  #    Propositional preprocessing time  : 0.000
% 0.11/0.38  #    Propositional encoding time       : 0.000
% 0.11/0.38  #    Propositional solver time         : 0.000
% 0.11/0.38  #    Success case prop preproc time    : 0.000
% 0.11/0.38  #    Success case prop encoding time   : 0.000
% 0.11/0.38  #    Success case prop solver time     : 0.000
% 0.11/0.38  # Current number of processed clauses  : 94
% 0.11/0.38  #    Positive orientable unit clauses  : 35
% 0.11/0.38  #    Positive unorientable unit clauses: 0
% 0.11/0.38  #    Negative unit clauses             : 5
% 0.11/0.38  #    Non-unit-clauses                  : 54
% 0.11/0.38  # Current number of unprocessed clauses: 5
% 0.11/0.38  # ...number of literals in the above   : 48
% 0.11/0.38  # Current number of archived formulas  : 0
% 0.11/0.38  # Current number of archived clauses   : 45
% 0.11/0.38  # Clause-clause subsumption calls (NU) : 4738
% 0.11/0.38  # Rec. Clause-clause subsumption calls : 294
% 0.11/0.38  # Non-unit clause-clause subsumptions  : 16
% 0.11/0.38  # Unit Clause-clause subsumption calls : 83
% 0.11/0.38  # Rewrite failures with RHS unbound    : 0
% 0.11/0.38  # BW rewrite match attempts            : 25
% 0.11/0.38  # BW rewrite match successes           : 3
% 0.11/0.38  # Condensation attempts                : 0
% 0.11/0.38  # Condensation successes               : 0
% 0.11/0.38  # Termbank termtop insertions          : 8009
% 0.11/0.38  
% 0.11/0.38  # -------------------------------------------------
% 0.11/0.38  # User time                : 0.047 s
% 0.11/0.38  # System time              : 0.001 s
% 0.11/0.38  # Total time               : 0.048 s
% 0.11/0.38  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

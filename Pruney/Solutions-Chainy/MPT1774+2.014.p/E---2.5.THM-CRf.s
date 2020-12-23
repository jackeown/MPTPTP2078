%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 554 expanded)
%              Number of clauses        :   63 ( 202 expanded)
%              Number of leaves         :   10 ( 132 expanded)
%              Depth                    :   15
%              Number of atoms          :  518 (7392 expanded)
%              Number of equality atoms :   20 ( 299 expanded)
%              Maximal formula depth    :   33 (   7 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_13,negated_conjecture,
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

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_17,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_26,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r1_tmap_1(X36,X34,X37,X39)
        | r1_tmap_1(X35,X34,k3_tmap_1(X33,X34,X36,X35,X37),X40)
        | ~ v3_pre_topc(X38,X36)
        | ~ r2_hidden(X39,X38)
        | ~ r1_tarski(X38,u1_struct_0(X35))
        | X39 != X40
        | ~ m1_subset_1(X40,u1_struct_0(X35))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X35,X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X34))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X34))))
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r1_tmap_1(X35,X34,k3_tmap_1(X33,X34,X36,X35,X37),X40)
        | r1_tmap_1(X36,X34,X37,X39)
        | ~ v3_pre_topc(X38,X36)
        | ~ r2_hidden(X39,X38)
        | ~ r1_tarski(X38,u1_struct_0(X35))
        | X39 != X40
        | ~ m1_subset_1(X40,u1_struct_0(X35))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X35,X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X34))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X34))))
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] :
      ( ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_pre_topc(X25,X24)
      | m1_pre_topc(X25,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk4_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44,X45] :
      ( ( ~ v3_pre_topc(X45,X42)
        | v3_pre_topc(X44,X41)
        | ~ v3_pre_topc(X43,X41)
        | ~ r1_tarski(X43,u1_struct_0(X42))
        | ~ r1_tarski(X44,X43)
        | X44 != X45
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_pre_topc(X42,X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( ~ v3_pre_topc(X44,X41)
        | v3_pre_topc(X45,X42)
        | ~ v3_pre_topc(X43,X41)
        | ~ r1_tarski(X43,u1_struct_0(X42))
        | ~ r1_tarski(X44,X43)
        | X44 != X45
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_pre_topc(X42,X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_tsep_1])])])])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),X2)
    | r1_tarski(esk7_0,X1)
    | ~ r1_tarski(u1_struct_0(esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ v3_pre_topc(X7,X1)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ r2_hidden(X4,X7)
    | ~ r1_tarski(X7,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk5_0))
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X3,X4)
    | ~ v3_pre_topc(X1,X4)
    | ~ v2_pre_topc(X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ l1_pre_topc(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v3_pre_topc(X4,esk5_0)
    | ~ r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X3,esk6_0),X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X3,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(X4,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])]),c_0_44]),c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(esk7_0,u1_struct_0(X2))
    | ~ r1_tarski(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_19]),c_0_51])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

fof(c_0_60,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X26)
      | v2_struct_0(X29)
      | ~ m1_pre_topc(X29,X26)
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X27))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X27))))
      | ~ m1_subset_1(X31,u1_struct_0(X28))
      | ~ m1_subset_1(X32,u1_struct_0(X29))
      | X31 != X32
      | ~ m1_pre_topc(X29,X28)
      | ~ r1_tmap_1(X28,X27,X30,X31)
      | r1_tmap_1(X29,X27,k3_tmap_1(X26,X27,X28,X29,X30),X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(esk7_0,esk5_0)
    | ~ r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ r1_tarski(esk7_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk7_0,X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_51]),c_0_59])]),c_0_29])).

cnf(c_0_64,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(esk7_0,esk5_0)
    | ~ r1_tmap_1(X2,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,X2,esk6_0),esk8_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X2))
    | ~ r1_tarski(esk7_0,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_18]),c_0_62])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_68,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_70,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,X5,X6)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X4)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_64,c_0_33])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ r1_tarski(esk7_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_76,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])]),c_0_44]),c_0_45])).

cnf(c_0_77,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_50]),c_0_18]),c_0_24]),c_0_19]),c_0_73]),c_0_21])]),c_0_74]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_79,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_55])])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_24]),c_0_73])]),c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_77])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_18]),c_0_50]),c_0_19])]),c_0_82]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.030 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t85_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(t84_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.13/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.39  fof(t9_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>((((v3_pre_topc(X3,X1)&r1_tarski(X3,u1_struct_0(X2)))&r1_tarski(X4,X3))&X4=X5)=>(v3_pre_topc(X5,X2)<=>v3_pre_topc(X4,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tsep_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t81_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((X6=X7&m1_pre_topc(X4,X3))&r1_tmap_1(X3,X2,X5,X6))=>r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 0.13/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t85_tmap_1])).
% 0.13/0.39  fof(c_0_11, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_12, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|l1_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk4_0))&((((v3_pre_topc(esk7_0,esk3_0)&r2_hidden(esk8_0,esk7_0))&r1_tarski(esk7_0,u1_struct_0(esk4_0)))&esk8_0=esk9_0)&((~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0))&(r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.13/0.39  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  fof(c_0_16, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.39  cnf(c_0_17, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_22, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_23, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.13/0.39  fof(c_0_26, plain, ![X33, X34, X35, X36, X37, X38, X39, X40]:((~r1_tmap_1(X36,X34,X37,X39)|r1_tmap_1(X35,X34,k3_tmap_1(X33,X34,X36,X35,X37),X40)|(~v3_pre_topc(X38,X36)|~r2_hidden(X39,X38)|~r1_tarski(X38,u1_struct_0(X35))|X39!=X40)|~m1_subset_1(X40,u1_struct_0(X35))|~m1_subset_1(X39,u1_struct_0(X36))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_pre_topc(X35,X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X34))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X34)))))|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~r1_tmap_1(X35,X34,k3_tmap_1(X33,X34,X36,X35,X37),X40)|r1_tmap_1(X36,X34,X37,X39)|(~v3_pre_topc(X38,X36)|~r2_hidden(X39,X38)|~r1_tarski(X38,u1_struct_0(X35))|X39!=X40)|~m1_subset_1(X40,u1_struct_0(X35))|~m1_subset_1(X39,u1_struct_0(X36))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_pre_topc(X35,X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X34))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X34)))))|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).
% 0.13/0.39  fof(c_0_27, plain, ![X23, X24, X25]:(~v2_pre_topc(X23)|~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|(~m1_pre_topc(X25,X24)|m1_pre_topc(X25,X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk4_0))|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.13/0.39  fof(c_0_31, plain, ![X41, X42, X43, X44, X45]:((~v3_pre_topc(X45,X42)|v3_pre_topc(X44,X41)|(~v3_pre_topc(X43,X41)|~r1_tarski(X43,u1_struct_0(X42))|~r1_tarski(X44,X43)|X44!=X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_pre_topc(X42,X41)|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(~v3_pre_topc(X44,X41)|v3_pre_topc(X45,X42)|(~v3_pre_topc(X43,X41)|~r1_tarski(X43,u1_struct_0(X42))|~r1_tarski(X44,X43)|X44!=X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X41)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_pre_topc(X42,X41)|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_tsep_1])])])])).
% 0.13/0.39  cnf(c_0_32, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~v3_pre_topc(X8,X4)|~r2_hidden(X7,X8)|~r1_tarski(X8,u1_struct_0(X1))|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_33, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),X2)|r1_tarski(esk7_0,X1)|~r1_tarski(u1_struct_0(esk4_0),X2)), inference(spm,[status(thm)],[c_0_14, c_0_28])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.39  cnf(c_0_36, plain, (v3_pre_topc(X3,X4)|~v3_pre_topc(X1,X2)|~v3_pre_topc(X5,X2)|~r1_tarski(X5,u1_struct_0(X4))|~r1_tarski(X1,X5)|X1!=X3|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  fof(c_0_37, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  cnf(c_0_38, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~v3_pre_topc(X7,X1)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~r2_hidden(X4,X7)|~r1_tarski(X7,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_32, c_0_33])])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),u1_struct_0(esk5_0))|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_48, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X3,X4)|~v3_pre_topc(X1,X4)|~v2_pre_topc(X4)|~m1_pre_topc(X2,X4)|~l1_pre_topc(X4)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X4)))|~r1_tarski(X3,u1_struct_0(X2))|~r1_tarski(X1,X3)), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (v3_pre_topc(esk7_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v3_pre_topc(X4,esk5_0)|~r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X3,esk6_0),X1)|~v2_pre_topc(X2)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X3,esk5_0)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X1,X4)|~r1_tarski(X4,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])]), c_0_44]), c_0_45])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,esk3_0)|~m1_pre_topc(X2,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(esk7_0,u1_struct_0(X2))|~r1_tarski(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_19]), c_0_51])])).
% 0.13/0.39  cnf(c_0_59, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.13/0.39  fof(c_0_60, plain, ![X26, X27, X28, X29, X30, X31, X32]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~m1_pre_topc(X28,X26)|(v2_struct_0(X29)|~m1_pre_topc(X29,X26)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X27))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X27))))|(~m1_subset_1(X31,u1_struct_0(X28))|(~m1_subset_1(X32,u1_struct_0(X29))|(X31!=X32|~m1_pre_topc(X29,X28)|~r1_tmap_1(X28,X27,X30,X31)|r1_tmap_1(X29,X27,k3_tmap_1(X26,X27,X28,X29,X30),X32))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~v3_pre_topc(esk7_0,esk5_0)|~r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)|~v2_pre_topc(X2)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X1,esk5_0)|~l1_pre_topc(X2)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(esk8_0,u1_struct_0(X1))|~r1_tarski(esk7_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (v3_pre_topc(esk7_0,X1)|~m1_pre_topc(X1,esk3_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_51]), c_0_59])]), c_0_29])).
% 0.13/0.39  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,u1_struct_0(X4))|X6!=X7|~m1_pre_topc(X4,X3)|~r1_tmap_1(X3,X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~v3_pre_topc(esk7_0,esk5_0)|~r1_tmap_1(X2,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,X2,esk6_0),esk8_0)|~v2_pre_topc(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,esk5_0)|~l1_pre_topc(X1)|~m1_subset_1(esk8_0,u1_struct_0(X2))|~r1_tarski(esk7_0,u1_struct_0(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_18]), c_0_62])])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_70, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X4,X2,X5,X6)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X5)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X4))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_64, c_0_33])])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)|~v2_pre_topc(X2)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X1,esk5_0)|~l1_pre_topc(X2)|~m1_subset_1(esk8_0,u1_struct_0(X1))|~r1_tarski(esk7_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_69, c_0_68])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(esk5_0,esk2_0,esk6_0,X3)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk5_0)|~m1_pre_topc(esk5_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43])]), c_0_44]), c_0_45])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_50]), c_0_18]), c_0_24]), c_0_19]), c_0_73]), c_0_21])]), c_0_74]), c_0_75])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk5_0,X1,esk6_0),esk8_0)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk5_0)|~m1_pre_topc(esk5_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_55])])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_78, c_0_68])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(X1,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_24]), c_0_73])]), c_0_74])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_77])])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_18]), c_0_50]), c_0_19])]), c_0_82]), c_0_75]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 84
% 0.13/0.39  # Proof object clause steps            : 63
% 0.13/0.39  # Proof object formula steps           : 21
% 0.13/0.39  # Proof object conjectures             : 49
% 0.13/0.39  # Proof object clause conjectures      : 46
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 34
% 0.13/0.39  # Proof object initial formulas used   : 10
% 0.13/0.39  # Proof object generating inferences   : 19
% 0.13/0.39  # Proof object simplifying inferences  : 64
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 10
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 39
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 39
% 0.13/0.39  # Processed clauses                    : 163
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 11
% 0.13/0.39  # ...remaining for further processing  : 151
% 0.13/0.39  # Other redundant clauses eliminated   : 7
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 8
% 0.13/0.39  # Generated clauses                    : 119
% 0.13/0.39  # ...of the previous two non-trivial   : 94
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 112
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 7
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 99
% 0.13/0.39  #    Positive orientable unit clauses  : 38
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 5
% 0.13/0.39  #    Non-unit-clauses                  : 56
% 0.13/0.39  # Current number of unprocessed clauses: 7
% 0.13/0.39  # ...number of literals in the above   : 49
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 45
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 5543
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 389
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 15
% 0.13/0.39  # Unit Clause-clause subsumption calls : 88
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 18
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 8116
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.046 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

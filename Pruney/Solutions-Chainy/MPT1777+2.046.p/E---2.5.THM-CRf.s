%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 283 expanded)
%              Number of clauses        :   53 (  99 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  391 (2997 expanded)
%              Number of equality atoms :   25 ( 286 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_tmap_1,conjecture,(
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
                     => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                 => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

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

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t86_tmap_1,axiom,(
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
                     => ( ( v1_tsep_1(X3,X4)
                          & m1_pre_topc(X3,X4) )
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( X6 = X7
                                 => ( r1_tmap_1(X4,X2,X5,X6)
                                  <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

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

fof(t60_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                   => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tmap_1])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ( ~ m1_pre_topc(X20,X21)
        | m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | m1_pre_topc(X20,X21)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | l1_pre_topc(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = esk4_0
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk6_0 = esk7_0
    & r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)
    & ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] :
      ( ( ~ r1_tmap_1(X35,X33,X36,X37)
        | r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X38)
        | X37 != X38
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ v1_tsep_1(X34,X35)
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
      & ( ~ r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X38)
        | r1_tmap_1(X35,X33,X36,X37)
        | X37 != X38
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ v1_tsep_1(X34,X35)
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).

fof(c_0_22,plain,(
    ! [X29,X30,X31] :
      ( ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | ~ m1_pre_topc(X31,X30)
      | m1_pre_topc(X31,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X18,X19] :
      ( ( v3_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
        | ~ v3_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))
        | ~ v3_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v3_pre_topc(X19,X18)
        | ~ v3_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v3_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

cnf(c_0_28,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ v1_tsep_1(X1,X4)
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_37,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | m1_pre_topc(X28,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_38,plain,
    ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26]),c_0_29])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X22] :
      ( ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | v3_pre_topc(k2_struct_0(X22),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_43,plain,(
    ! [X14] :
      ( ~ l1_struct_0(X14)
      | k2_struct_0(X14) = u1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_44,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_45,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_tsep_1(X6,X1)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_56,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_58,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_tsep_1(X24,X23)
        | ~ m1_pre_topc(X24,X23)
        | v3_pre_topc(X25,X23)
        | X25 != u1_struct_0(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( v1_tsep_1(X24,X23)
        | ~ v3_pre_topc(X25,X23)
        | X25 != u1_struct_0(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_pre_topc(X24,X23)
        | ~ v3_pre_topc(X25,X23)
        | X25 != u1_struct_0(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_59,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | m1_subset_1(u1_struct_0(X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_36]),c_0_39])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_62,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_63,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,esk5_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk4_0,X3,esk5_0),X1)
    | ~ v1_tsep_1(X3,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X3,esk4_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])]),c_0_51]),c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_36])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_74,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_75,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_76,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_77,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),c_0_26]),c_0_29]),c_0_69]),c_0_70])]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_79,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_36]),c_0_39])])).

cnf(c_0_81,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_67]),c_0_26])])).

cnf(c_0_82,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_67]),c_0_26]),c_0_29])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_68]),c_0_81]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.030 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.19/0.38  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.38  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(t86_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_tsep_1(X3,X4)&m1_pre_topc(X3,X4))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(X6=X7=>(r1_tmap_1(X4,X2,X5,X6)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 0.19/0.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.38  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.38  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.19/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.19/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.19/0.38  fof(c_0_16, plain, ![X20, X21]:((~m1_pre_topc(X20,X21)|m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(~m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|m1_pre_topc(X20,X21)|~l1_pre_topc(X21)|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.38  fof(c_0_17, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|l1_pre_topc(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.38  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=esk4_0&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&((esk6_0=esk7_0&r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0))&~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk6_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.38  fof(c_0_19, plain, ![X12, X13]:(~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|v2_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.38  fof(c_0_20, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_21, plain, ![X32, X33, X34, X35, X36, X37, X38]:((~r1_tmap_1(X35,X33,X36,X37)|r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X38)|X37!=X38|~m1_subset_1(X38,u1_struct_0(X34))|~m1_subset_1(X37,u1_struct_0(X35))|(~v1_tsep_1(X34,X35)|~m1_pre_topc(X34,X35))|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X35),u1_struct_0(X33))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~r1_tmap_1(X34,X33,k3_tmap_1(X32,X33,X35,X34,X36),X38)|r1_tmap_1(X35,X33,X36,X37)|X37!=X38|~m1_subset_1(X38,u1_struct_0(X34))|~m1_subset_1(X37,u1_struct_0(X35))|(~v1_tsep_1(X34,X35)|~m1_pre_topc(X34,X35))|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X35),u1_struct_0(X33))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).
% 0.19/0.38  fof(c_0_22, plain, ![X29, X30, X31]:(~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|(~m1_pre_topc(X31,X30)|m1_pre_topc(X31,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.38  cnf(c_0_23, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_27, plain, ![X18, X19]:(((v3_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|(~v3_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))|(~v3_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))&((v3_pre_topc(X19,X18)|(~v3_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(~v3_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.19/0.38  cnf(c_0_28, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_30, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_32, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~v1_tsep_1(X1,X4)|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_33, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_34, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=esk4_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.19/0.39  fof(c_0_37, plain, ![X28]:(~l1_pre_topc(X28)|m1_pre_topc(X28,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.39  cnf(c_0_38, plain, (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_26]), c_0_29])])).
% 0.19/0.39  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.19/0.39  fof(c_0_42, plain, ![X22]:(~v2_pre_topc(X22)|~l1_pre_topc(X22)|v3_pre_topc(k2_struct_0(X22),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.19/0.39  fof(c_0_43, plain, ![X14]:(~l1_struct_0(X14)|k2_struct_0(X14)=u1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.39  fof(c_0_44, plain, ![X15]:(~l1_pre_topc(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.39  cnf(c_0_45, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v1_tsep_1(X6,X1)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_32, c_0_33])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.39  cnf(c_0_56, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_58, plain, ![X23, X24, X25]:((~v1_tsep_1(X24,X23)|~m1_pre_topc(X24,X23)|v3_pre_topc(X25,X23)|X25!=u1_struct_0(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&((v1_tsep_1(X24,X23)|~v3_pre_topc(X25,X23)|X25!=u1_struct_0(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(m1_pre_topc(X24,X23)|~v3_pre_topc(X25,X23)|X25!=u1_struct_0(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.19/0.39  fof(c_0_59, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_pre_topc(X27,X26)|m1_subset_1(u1_struct_0(X27),k1_zfmisc_1(u1_struct_0(X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_36]), c_0_39])])).
% 0.19/0.39  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_62, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_63, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  cnf(c_0_64, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,esk5_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk4_0,X3,esk5_0),X1)|~v1_tsep_1(X3,esk4_0)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X3,esk4_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])]), c_0_51]), c_0_52])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_36])])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_57, c_0_54])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_74, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.39  cnf(c_0_75, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk4_0)|~v3_pre_topc(u1_struct_0(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.39  cnf(c_0_77, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, (~v1_tsep_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), c_0_26]), c_0_29]), c_0_69]), c_0_70])]), c_0_71]), c_0_72]), c_0_73])).
% 0.19/0.39  cnf(c_0_79, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_75])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (v3_pre_topc(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_36]), c_0_39])])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_67]), c_0_26])])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_67]), c_0_26]), c_0_29])])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_68]), c_0_81]), c_0_82])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 84
% 0.19/0.39  # Proof object clause steps            : 53
% 0.19/0.39  # Proof object formula steps           : 31
% 0.19/0.39  # Proof object conjectures             : 36
% 0.19/0.39  # Proof object clause conjectures      : 33
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 33
% 0.19/0.39  # Proof object initial formulas used   : 15
% 0.19/0.39  # Proof object generating inferences   : 14
% 0.19/0.39  # Proof object simplifying inferences  : 51
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 15
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 43
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 42
% 0.19/0.39  # Processed clauses                    : 130
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 3
% 0.19/0.39  # ...remaining for further processing  : 127
% 0.19/0.39  # Other redundant clauses eliminated   : 6
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 105
% 0.19/0.39  # ...of the previous two non-trivial   : 66
% 0.19/0.39  # Contextual simplify-reflections      : 6
% 0.19/0.39  # Paramodulations                      : 99
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 6
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 79
% 0.19/0.39  #    Positive orientable unit clauses  : 22
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 6
% 0.19/0.39  #    Non-unit-clauses                  : 51
% 0.19/0.39  # Current number of unprocessed clauses: 19
% 0.19/0.39  # ...number of literals in the above   : 113
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 42
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1347
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 209
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.19/0.39  # Unit Clause-clause subsumption calls : 31
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 3
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 5803
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.038 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.042 s
% 0.19/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

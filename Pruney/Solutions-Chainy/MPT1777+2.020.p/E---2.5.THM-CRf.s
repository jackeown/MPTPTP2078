%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 367 expanded)
%              Number of clauses        :   61 ( 128 expanded)
%              Number of leaves         :   17 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  474 (3886 expanded)
%              Number of equality atoms :   34 ( 375 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t19_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tsep_1(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
               => ( v1_tsep_1(X2,X3)
                  & m1_pre_topc(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t31_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( l1_pre_topc(X3)
             => ! [X4] :
                  ( l1_pre_topc(X4)
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
                      & m1_pre_topc(X3,X1) )
                   => m1_pre_topc(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(fc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | l1_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_19,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X32,X33,X34] :
      ( ( ~ r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | m1_pre_topc(X33,X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_pre_topc(X33,X34)
        | r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_21,plain,(
    ! [X35,X36,X37] :
      ( ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | ~ m1_pre_topc(X37,X36)
      | m1_pre_topc(X37,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_22,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | m1_pre_topc(X31,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_23,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | v2_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_27,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_33,plain,(
    ! [X21,X22] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)),X21)
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_35,plain,(
    ! [X26,X27,X28] :
      ( ( v1_tsep_1(X27,X28)
        | ~ r1_tarski(u1_struct_0(X27),u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | ~ v1_tsep_1(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_pre_topc(X27,X28)
        | ~ r1_tarski(u1_struct_0(X27),u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | ~ v1_tsep_1(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_tsep_1])])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_32]),c_0_25])])).

cnf(c_0_39,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_34]),c_0_25])])).

fof(c_0_42,plain,(
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

fof(c_0_43,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | m1_subset_1(u1_struct_0(X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_44,plain,(
    ! [X20] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | v3_pre_topc(k2_struct_0(X20),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_45,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | k2_struct_0(X11) = u1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_46,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_47,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ l1_pre_topc(X16)
      | ~ l1_pre_topc(X17)
      | ~ l1_pre_topc(X18)
      | ~ l1_pre_topc(X19)
      | g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)) != g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))
      | g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)) != g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))
      | ~ m1_pre_topc(X18,X16)
      | m1_pre_topc(X19,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_pre_topc])])])).

fof(c_0_48,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] :
      ( ( ~ r1_tmap_1(X41,X39,X42,X43)
        | r1_tmap_1(X40,X39,k3_tmap_1(X38,X39,X41,X40,X42),X44)
        | X43 != X44
        | ~ m1_subset_1(X44,u1_struct_0(X40))
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | ~ v1_tsep_1(X40,X41)
        | ~ m1_pre_topc(X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,u1_struct_0(X41),u1_struct_0(X39))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X39))))
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r1_tmap_1(X40,X39,k3_tmap_1(X38,X39,X41,X40,X42),X44)
        | r1_tmap_1(X41,X39,X42,X43)
        | X43 != X44
        | ~ m1_subset_1(X44,u1_struct_0(X40))
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | ~ v1_tsep_1(X40,X41)
        | ~ m1_pre_topc(X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,u1_struct_0(X41),u1_struct_0(X39))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X39))))
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X38)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).

cnf(c_0_49,plain,
    ( v1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ v1_tsep_1(X1,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_30])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

cnf(c_0_54,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X4)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( v1_tsep_1(X1,esk4_0)
    | v2_struct_0(X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_53])])).

cnf(c_0_63,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_34]),c_0_32]),c_0_25])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_55])).

cnf(c_0_66,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_67,plain,
    ( m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4) ),
    inference(csr,[status(thm)],[c_0_59,c_0_23])).

fof(c_0_68,plain,(
    ! [X15] :
      ( ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_pre_topc(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).

cnf(c_0_69,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_tsep_1(X6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_60,c_0_28])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_76,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_77,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( v1_tsep_1(X1,esk4_0)
    | ~ v1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_41])]),c_0_64])).

cnf(c_0_80,plain,
    ( v1_tsep_1(X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_29])).

cnf(c_0_81,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != esk4_0
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != esk4_0
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_40]),c_0_40]),c_0_41])])).

fof(c_0_82,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | ~ v1_pre_topc(X8)
      | X8 = g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_83,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,esk5_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk4_0,X3,esk5_0),X1)
    | ~ v1_tsep_1(X3,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X3,esk4_0)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72]),c_0_73]),c_0_74])]),c_0_75]),c_0_51])).

cnf(c_0_85,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_90,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_63]),c_0_41])])).

cnf(c_0_91,negated_conjecture,
    ( m1_pre_topc(esk3_0,X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != esk4_0
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_40]),c_0_41])])).

cnf(c_0_92,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_93,negated_conjecture,
    ( v1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_41]),c_0_40]),c_0_64])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87]),c_0_24]),c_0_32]),c_0_25])]),c_0_88]),c_0_89]),c_0_64]),c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92])]),c_0_30]),c_0_93])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.13/0.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.38  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.13/0.38  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.13/0.38  fof(t19_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))=>(v1_tsep_1(X2,X3)&m1_pre_topc(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 0.13/0.38  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.13/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.38  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.13/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(t31_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(l1_pre_topc(X3)=>![X4]:(l1_pre_topc(X4)=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))&m1_pre_topc(X3,X1))=>m1_pre_topc(X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 0.13/0.38  fof(t86_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_tsep_1(X3,X4)&m1_pre_topc(X3,X4))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(X6=X7=>(r1_tmap_1(X4,X2,X5,X6)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 0.13/0.38  fof(fc7_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>(~(v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))&v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 0.13/0.38  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|l1_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=esk4_0&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&((esk6_0=esk7_0&r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0))&~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk6_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X32, X33, X34]:((~r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|m1_pre_topc(X33,X34)|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~m1_pre_topc(X33,X34)|r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X35, X36, X37]:(~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|(~m1_pre_topc(X37,X36)|m1_pre_topc(X37,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X31]:(~l1_pre_topc(X31)|m1_pre_topc(X31,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.38  cnf(c_0_23, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_26, plain, ![X9, X10]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|v2_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_27, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.13/0.38  cnf(c_0_31, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_33, plain, ![X21, X22]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)),X21)|~m1_pre_topc(X22,X21)|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_35, plain, ![X26, X27, X28]:((v1_tsep_1(X27,X28)|~r1_tarski(u1_struct_0(X27),u1_struct_0(X28))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(~v1_tsep_1(X27,X26)|~m1_pre_topc(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(m1_pre_topc(X27,X28)|~r1_tarski(u1_struct_0(X27),u1_struct_0(X28))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(~v1_tsep_1(X27,X26)|~m1_pre_topc(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_tsep_1])])])])])).
% 0.13/0.38  cnf(c_0_36, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_32]), c_0_25])])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=esk4_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_34]), c_0_25])])).
% 0.13/0.38  fof(c_0_42, plain, ![X23, X24, X25]:((~v1_tsep_1(X24,X23)|~m1_pre_topc(X24,X23)|v3_pre_topc(X25,X23)|X25!=u1_struct_0(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&((v1_tsep_1(X24,X23)|~v3_pre_topc(X25,X23)|X25!=u1_struct_0(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(m1_pre_topc(X24,X23)|~v3_pre_topc(X25,X23)|X25!=u1_struct_0(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m1_pre_topc(X24,X23)|(~v2_pre_topc(X23)|~l1_pre_topc(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.13/0.38  fof(c_0_43, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|m1_subset_1(u1_struct_0(X30),k1_zfmisc_1(u1_struct_0(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.38  fof(c_0_44, plain, ![X20]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|v3_pre_topc(k2_struct_0(X20),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.13/0.38  fof(c_0_45, plain, ![X11]:(~l1_struct_0(X11)|k2_struct_0(X11)=u1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.38  fof(c_0_46, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  fof(c_0_47, plain, ![X16, X17, X18, X19]:(~l1_pre_topc(X16)|(~l1_pre_topc(X17)|(~l1_pre_topc(X18)|(~l1_pre_topc(X19)|(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))!=g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))|g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))!=g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))|~m1_pre_topc(X18,X16)|m1_pre_topc(X19,X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_pre_topc])])])).
% 0.13/0.38  fof(c_0_48, plain, ![X38, X39, X40, X41, X42, X43, X44]:((~r1_tmap_1(X41,X39,X42,X43)|r1_tmap_1(X40,X39,k3_tmap_1(X38,X39,X41,X40,X42),X44)|X43!=X44|~m1_subset_1(X44,u1_struct_0(X40))|~m1_subset_1(X43,u1_struct_0(X41))|(~v1_tsep_1(X40,X41)|~m1_pre_topc(X40,X41))|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X41),u1_struct_0(X39))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X39)))))|(v2_struct_0(X41)|~m1_pre_topc(X41,X38))|(v2_struct_0(X40)|~m1_pre_topc(X40,X38))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~r1_tmap_1(X40,X39,k3_tmap_1(X38,X39,X41,X40,X42),X44)|r1_tmap_1(X41,X39,X42,X43)|X43!=X44|~m1_subset_1(X44,u1_struct_0(X40))|~m1_subset_1(X43,u1_struct_0(X41))|(~v1_tsep_1(X40,X41)|~m1_pre_topc(X40,X41))|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X41),u1_struct_0(X39))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X39)))))|(v2_struct_0(X41)|~m1_pre_topc(X41,X38))|(v2_struct_0(X40)|~m1_pre_topc(X40,X38))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).
% 0.13/0.38  cnf(c_0_49, plain, (v1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~v1_tsep_1(X1,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_30])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_41])).
% 0.13/0.38  cnf(c_0_54, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_55, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_56, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_57, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_58, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_59, plain, (m1_pre_topc(X4,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X4)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))!=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_60, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~v1_tsep_1(X1,X4)|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (v1_tsep_1(X1,esk4_0)|v2_struct_0(X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,esk4_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_28])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_53])])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_34]), c_0_32]), c_0_25])])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_65, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_55])).
% 0.13/0.38  cnf(c_0_66, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.13/0.38  cnf(c_0_67, plain, (m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~m1_pre_topc(X3,X4)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X4)), inference(csr,[status(thm)],[c_0_59, c_0_23])).
% 0.13/0.38  fof(c_0_68, plain, ![X15]:((~v2_struct_0(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))|(v2_struct_0(X15)|~l1_pre_topc(X15)))&(v1_pre_topc(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))|(v2_struct_0(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).
% 0.13/0.38  cnf(c_0_69, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v1_tsep_1(X6,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~l1_pre_topc(X5)|~l1_pre_topc(X2)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_60, c_0_28])])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (v1_tsep_1(X1,esk4_0)|~v1_tsep_1(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_41])]), c_0_64])).
% 0.13/0.38  cnf(c_0_80, plain, (v1_tsep_1(X1,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_29])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=esk4_0|g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))!=esk4_0|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_53]), c_0_40]), c_0_40]), c_0_41])])).
% 0.13/0.38  fof(c_0_82, plain, ![X8]:(~l1_pre_topc(X8)|(~v1_pre_topc(X8)|X8=g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.13/0.38  cnf(c_0_83, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,esk5_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,esk2_0,k3_tmap_1(X2,esk2_0,esk4_0,X3,esk5_0),X1)|~v1_tsep_1(X3,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(X3))|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X3,esk4_0)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72]), c_0_73]), c_0_74])]), c_0_75]), c_0_51])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_78, c_0_77])).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_90, negated_conjecture, (v1_tsep_1(esk3_0,esk4_0)|~m1_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_63]), c_0_41])])).
% 0.13/0.38  cnf(c_0_91, negated_conjecture, (m1_pre_topc(esk3_0,X1)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=esk4_0|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_40]), c_0_41])])).
% 0.13/0.38  cnf(c_0_92, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.13/0.38  cnf(c_0_93, negated_conjecture, (v1_pre_topc(esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_41]), c_0_40]), c_0_64])).
% 0.13/0.38  cnf(c_0_94, negated_conjecture, (~m1_pre_topc(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_87]), c_0_24]), c_0_32]), c_0_25])]), c_0_88]), c_0_89]), c_0_64]), c_0_90])).
% 0.13/0.38  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92])]), c_0_30]), c_0_93])]), c_0_94]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 96
% 0.13/0.38  # Proof object clause steps            : 61
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 42
% 0.13/0.38  # Proof object clause conjectures      : 39
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 35
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 20
% 0.13/0.38  # Proof object simplifying inferences  : 64
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 42
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 41
% 0.13/0.38  # Processed clauses                    : 165
% 0.13/0.38  # ...of these trivial                  : 4
% 0.13/0.38  # ...subsumed                          : 14
% 0.13/0.38  # ...remaining for further processing  : 147
% 0.13/0.38  # Other redundant clauses eliminated   : 7
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 209
% 0.13/0.38  # ...of the previous two non-trivial   : 123
% 0.13/0.38  # Contextual simplify-reflections      : 13
% 0.13/0.38  # Paramodulations                      : 202
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 103
% 0.13/0.38  #    Positive orientable unit clauses  : 39
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 6
% 0.13/0.38  #    Non-unit-clauses                  : 58
% 0.13/0.38  # Current number of unprocessed clauses: 39
% 0.13/0.38  # ...number of literals in the above   : 118
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 40
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1965
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 284
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 26
% 0.13/0.38  # Unit Clause-clause subsumption calls : 15
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 36
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 8452
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.041 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.045 s
% 0.13/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

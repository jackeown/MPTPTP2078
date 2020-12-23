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
% DateTime   : Thu Dec  3 11:17:39 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 190 expanded)
%              Number of clauses        :   55 (  74 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  270 (1410 expanded)
%              Number of equality atoms :   34 ( 104 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_tmap_1,conjecture,(
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
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                           => ( r1_tarski(k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6),u1_struct_0(X3))
                             => k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6) = k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tmap_1)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

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
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                             => ( r1_tarski(k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6),u1_struct_0(X3))
                               => k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6) = k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tmap_1])).

fof(c_0_18,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | v2_struct_0(X46)
      | ~ v2_pre_topc(X46)
      | ~ l1_pre_topc(X46)
      | ~ m1_pre_topc(X47,X45)
      | ~ m1_pre_topc(X48,X45)
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X46))
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46))))
      | ~ m1_pre_topc(X48,X47)
      | k3_tmap_1(X45,X46,X47,X48,X49) = k2_partfun1(u1_struct_0(X47),u1_struct_0(X46),X49,u1_struct_0(X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

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
    & m1_pre_topc(esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r1_tarski(k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0),u1_struct_0(esk3_0))
    & k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0) != k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ v1_funct_1(X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k2_partfun1(X41,X42,X43,X44) = k7_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_30,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk5_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_36,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_37,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ r1_tarski(k1_relat_1(X40),X38)
      | ~ r1_tarski(k2_relat_1(X40),X39)
      | m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_38,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

fof(c_0_40,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k8_relset_1(X34,X35,X36,X37) = k10_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X18,X19] :
      ( ( ~ v5_relat_1(X19,X18)
        | r1_tarski(k2_relat_1(X19),X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(k2_relat_1(X19),X18)
        | v5_relat_1(X19,X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_44,plain,(
    ! [X31,X32,X33] :
      ( ( v4_relat_1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v5_relat_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_45,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_46,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0) != k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0) = k7_relat_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_25]),c_0_21])])).

cnf(c_0_48,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X3)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | r1_tarski(k1_relat_1(k7_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_52,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k7_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_53,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0) != k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,X1) = k10_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_64,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_relat_1(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_65,plain,(
    ! [X22,X23] : v1_relat_1(k2_zfmisc_1(X22,X23)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_66,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_67,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_68,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0) != k10_relat_1(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,plain,
    ( k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_70,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(X2,X3))
    | ~ v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( v5_relat_1(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_74,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X30)
      | k10_relat_1(k7_relat_1(X30,X28),X29) = k3_xboole_0(X28,k10_relat_1(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0) != k10_relat_1(esk5_0,esk6_0)
    | ~ r1_tarski(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(X2,u1_struct_0(esk2_0)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k7_relat_1(X1,X2),esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_21]),c_0_73])])).

cnf(c_0_80,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_83,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0) != k10_relat_1(esk5_0,esk6_0)
    | ~ r1_tarski(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_84,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,esk6_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_58])).

fof(c_0_86,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | r1_tarski(k7_relat_1(X27,X26),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_79]),c_0_85])])).

cnf(c_0_88,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:41:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t76_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6),u1_struct_0(X3))=>k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6)=k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tmap_1)).
% 0.19/0.41  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.19/0.41  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.41  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.19/0.41  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.41  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.19/0.41  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.19/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.41  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.19/0.41  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.19/0.41  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6),u1_struct_0(X3))=>k8_relset_1(u1_struct_0(X4),u1_struct_0(X2),X5,X6)=k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6)))))))))), inference(assume_negation,[status(cth)],[t76_tmap_1])).
% 0.19/0.41  fof(c_0_18, plain, ![X45, X46, X47, X48, X49]:(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)|(~m1_pre_topc(X47,X45)|(~m1_pre_topc(X48,X45)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X46))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46))))|(~m1_pre_topc(X48,X47)|k3_tmap_1(X45,X46,X47,X48,X49)=k2_partfun1(u1_struct_0(X47),u1_struct_0(X46),X49,u1_struct_0(X48)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.19/0.41  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk3_0,esk4_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_tarski(k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0),u1_struct_0(esk3_0))&k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0)!=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.19/0.41  cnf(c_0_20, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  fof(c_0_29, plain, ![X41, X42, X43, X44]:(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k2_partfun1(X41,X42,X43,X44)=k7_relat_1(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk5_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  fof(c_0_36, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  fof(c_0_37, plain, ![X38, X39, X40]:(~v1_relat_1(X40)|(~r1_tarski(k1_relat_1(X40),X38)|~r1_tarski(k2_relat_1(X40),X39)|m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.41  cnf(c_0_38, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))=k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.19/0.41  fof(c_0_40, plain, ![X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k8_relset_1(X34,X35,X36,X37)=k10_relat_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.19/0.41  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  fof(c_0_43, plain, ![X18, X19]:((~v5_relat_1(X19,X18)|r1_tarski(k2_relat_1(X19),X18)|~v1_relat_1(X19))&(~r1_tarski(k2_relat_1(X19),X18)|v5_relat_1(X19,X18)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.41  fof(c_0_44, plain, ![X31, X32, X33]:((v4_relat_1(X33,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v5_relat_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.41  fof(c_0_45, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X10,X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0)!=k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0)=k7_relat_1(esk5_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_25]), c_0_21])])).
% 0.19/0.41  cnf(c_0_48, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.41  cnf(c_0_49, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X3)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_50, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  fof(c_0_51, plain, ![X24, X25]:(~v1_relat_1(X25)|r1_tarski(k1_relat_1(k7_relat_1(X25,X24)),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.19/0.41  fof(c_0_52, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k7_relat_1(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.19/0.41  cnf(c_0_53, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.41  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_55, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_41, c_0_21])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0)!=k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,X1)=k10_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_21])).
% 0.19/0.41  cnf(c_0_59, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v5_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.41  cnf(c_0_60, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.41  cnf(c_0_61, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_62, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.41  fof(c_0_64, plain, ![X16, X17]:(~v1_relat_1(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_relat_1(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.41  fof(c_0_65, plain, ![X22, X23]:v1_relat_1(k2_zfmisc_1(X22,X23)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.41  fof(c_0_66, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.41  fof(c_0_67, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0)!=k10_relat_1(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.41  cnf(c_0_69, plain, (k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.19/0.41  cnf(c_0_70, plain, (r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(X2,X3))|~v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (v5_relat_1(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.41  cnf(c_0_72, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.41  cnf(c_0_73, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.41  fof(c_0_74, plain, ![X28, X29, X30]:(~v1_relat_1(X30)|k10_relat_1(k7_relat_1(X30,X28),X29)=k3_xboole_0(X28,k10_relat_1(X30,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.19/0.41  cnf(c_0_75, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.41  cnf(c_0_76, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (k10_relat_1(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0)!=k10_relat_1(esk5_0,esk6_0)|~r1_tarski(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (r1_tarski(k7_relat_1(X1,X2),k2_zfmisc_1(X2,u1_struct_0(esk2_0)))|~v1_relat_1(X1)|~r1_tarski(k7_relat_1(X1,X2),esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_21]), c_0_73])])).
% 0.19/0.41  cnf(c_0_80, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.41  cnf(c_0_81, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (r1_tarski(k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (k10_relat_1(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk6_0)!=k10_relat_1(esk5_0,esk6_0)|~r1_tarski(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.19/0.41  cnf(c_0_84, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X3),X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,esk6_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_82, c_0_58])).
% 0.19/0.41  fof(c_0_86, plain, ![X26, X27]:(~v1_relat_1(X27)|r1_tarski(k7_relat_1(X27,X26),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (~r1_tarski(k7_relat_1(esk5_0,u1_struct_0(esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_79]), c_0_85])])).
% 0.19/0.41  cnf(c_0_88, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_79])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 90
% 0.19/0.41  # Proof object clause steps            : 55
% 0.19/0.41  # Proof object formula steps           : 35
% 0.19/0.41  # Proof object conjectures             : 34
% 0.19/0.41  # Proof object clause conjectures      : 31
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 31
% 0.19/0.41  # Proof object initial formulas used   : 17
% 0.19/0.41  # Proof object generating inferences   : 21
% 0.19/0.41  # Proof object simplifying inferences  : 27
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 17
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 36
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 36
% 0.19/0.41  # Processed clauses                    : 393
% 0.19/0.41  # ...of these trivial                  : 2
% 0.19/0.41  # ...subsumed                          : 45
% 0.19/0.41  # ...remaining for further processing  : 346
% 0.19/0.41  # Other redundant clauses eliminated   : 0
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 2
% 0.19/0.41  # Backward-rewritten                   : 17
% 0.19/0.41  # Generated clauses                    : 1052
% 0.19/0.41  # ...of the previous two non-trivial   : 1034
% 0.19/0.41  # Contextual simplify-reflections      : 10
% 0.19/0.41  # Paramodulations                      : 1052
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 0
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 291
% 0.19/0.41  #    Positive orientable unit clauses  : 49
% 0.19/0.41  #    Positive unorientable unit clauses: 1
% 0.19/0.41  #    Negative unit clauses             : 6
% 0.19/0.41  #    Non-unit-clauses                  : 235
% 0.19/0.41  # Current number of unprocessed clauses: 710
% 0.19/0.41  # ...number of literals in the above   : 3000
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 55
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 16685
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 5223
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 57
% 0.19/0.41  # Unit Clause-clause subsumption calls : 412
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 39
% 0.19/0.41  # BW rewrite match successes           : 13
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 27773
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.076 s
% 0.19/0.41  # System time              : 0.009 s
% 0.19/0.41  # Total time               : 0.086 s
% 0.19/0.41  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

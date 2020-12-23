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
% DateTime   : Thu Dec  3 11:14:03 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  144 (13684 expanded)
%              Number of clauses        :  103 (4870 expanded)
%              Number of leaves         :   20 (3378 expanded)
%              Depth                    :   22
%              Number of atoms          :  444 (76778 expanded)
%              Number of equality atoms :  145 (19339 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v2_funct_1(X3) )
                   => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t67_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v2_funct_1(X3) )
                   => k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(t63_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t48_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_struct_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                        & v2_funct_1(X3) )
                     => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_tops_2])).

fof(c_0_21,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X39] :
      ( ~ l1_struct_0(X39)
      | k2_struct_0(X39) = u1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_23,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ l1_struct_0(X49)
      | ~ l1_struct_0(X50)
      | ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X49)))
      | k2_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51) != k2_struct_0(X50)
      | ~ v2_funct_1(X51)
      | k7_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52) = k8_relset_1(u1_struct_0(X50),u1_struct_0(X49),k2_tops_2(u1_struct_0(X49),u1_struct_0(X50),X51),X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).

fof(c_0_24,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X40,X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k2_relset_1(X40,X41,X42) != X41
      | ~ v2_funct_1(X42)
      | k2_tops_2(X40,X41,X42) = k2_funct_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

fof(c_0_25,plain,(
    ! [X46,X47,X48] :
      ( ~ l1_struct_0(X46)
      | ~ l1_struct_0(X47)
      | ~ v1_funct_1(X48)
      | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47))))
      | k2_relset_1(u1_struct_0(X46),u1_struct_0(X47),X48) != k2_struct_0(X47)
      | ~ v2_funct_1(X48)
      | v2_funct_1(k2_tops_2(u1_struct_0(X46),u1_struct_0(X47),X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).

cnf(c_0_26,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ v2_funct_1(X14)
      | k2_funct_1(k2_funct_1(X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_32,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_34,plain,(
    ! [X33,X34,X35] :
      ( ( v1_funct_1(k2_funct_1(X35))
        | ~ v2_funct_1(X35)
        | k2_relset_1(X33,X34,X35) != X34
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v1_funct_2(k2_funct_1(X35),X34,X33)
        | ~ v2_funct_1(X35)
        | k2_relset_1(X33,X34,X35) != X34
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( m1_subset_1(k2_funct_1(X35),k1_zfmisc_1(k2_zfmisc_1(X34,X33)))
        | ~ v2_funct_1(X35)
        | k2_relset_1(X33,X34,X35) != X34
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_35,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_36,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,plain,
    ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3),X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != u1_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != u1_struct_0(X3)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
    ! [X13] :
      ( ( k2_relat_1(X13) = k1_relat_1(k2_funct_1(X13))
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_relat_1(X13) = k2_relat_1(k2_funct_1(X13))
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_49,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k2_relset_1(X27,X28,X29) = k2_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_50,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | m1_subset_1(k2_relset_1(X21,X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_51,plain,(
    ! [X10] : m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_52,plain,(
    ! [X9] : k2_subset_1(X9) = X9 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_53,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0),esk4_0) != k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_33]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_54,plain,
    ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3),X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3)) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3)) != u1_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(k2_funct_1(X3),u1_struct_0(X1),u1_struct_0(X2))
    | ~ v2_funct_1(k2_funct_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(k2_funct_1(X3))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_33]),c_0_44]),c_0_33]),c_0_28]),c_0_45]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_33]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_61,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_62,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_63,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_66,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_67,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | m1_subset_1(k1_relset_1(X18,X19,X20),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_68,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_relset_1(X24,X25,X26) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_69,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_45]),c_0_28]),c_0_55]),c_0_38]),c_0_56]),c_0_39]),c_0_57]),c_0_58])])).

cnf(c_0_70,plain,
    ( k2_relset_1(X1,X2,k2_funct_1(X3)) = k1_relat_1(X3)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_71,plain,(
    ! [X36,X37,X38] :
      ( ( X37 = k1_xboole_0
        | k8_relset_1(X36,X37,X38,X37) = X36
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X36 != k1_xboole_0
        | k8_relset_1(X36,X37,X38,X37) = X36
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X36,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).

fof(c_0_72,plain,(
    ! [X30,X31,X32] :
      ( ( k7_relset_1(X30,X31,X32,X30) = k2_relset_1(X30,X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( k8_relset_1(X30,X31,X32,X31) = k1_relset_1(X30,X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_60])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( k1_relat_1(esk3_0) != k2_struct_0(esk1_0)
    | k1_relat_1(esk3_0) != u1_struct_0(esk1_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_38]),c_0_39]),c_0_57])])).

cnf(c_0_81,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,X1) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_87,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_89,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_60])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(esk3_0) != k2_struct_0(esk1_0)
    | k1_relat_1(esk3_0) != u1_struct_0(esk1_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_33]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_91,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_92,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk2_0)) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_40]),c_0_37]),c_0_39])])).

cnf(c_0_93,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relat_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_83])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_74])).

cnf(c_0_95,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_96,plain,
    ( m1_subset_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_76])).

cnf(c_0_97,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( k2_relset_1(X1,X2,esk3_0) = u1_struct_0(esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_89]),c_0_40])])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk3_0) != k2_struct_0(esk1_0)
    | k1_relat_1(esk3_0) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_33]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_100,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_40])])).

cnf(c_0_101,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_95])).

cnf(c_0_103,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( k2_relat_1(esk3_0) = u1_struct_0(esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk1_0) != u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,plain,
    ( k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_107,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_103])).

cnf(c_0_108,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_86])).

cnf(c_0_109,negated_conjecture,
    ( k2_relat_1(esk3_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_40])).

cnf(c_0_110,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_27]),c_0_45])])).

cnf(c_0_111,plain,
    ( k2_relat_1(k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107]),c_0_107])).

cnf(c_0_112,plain,
    ( X1 = k2_relat_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( k2_relat_1(esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_110]),c_0_97])).

cnf(c_0_115,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k1_xboole_0))
    | k2_relset_1(X2,k1_xboole_0,X1) != k1_xboole_0
    | ~ v1_funct_2(X1,X2,k1_xboole_0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_86]),c_0_97])).

cnf(c_0_116,plain,
    ( k2_relset_1(X1,X2,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_111]),c_0_103])])).

cnf(c_0_117,negated_conjecture,
    ( X1 = u1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_109])).

cnf(c_0_118,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_97])).

cnf(c_0_119,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])])).

cnf(c_0_120,plain,
    ( m1_subset_1(k2_funct_1(k1_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_relat_1(k1_xboole_0),X1,k1_xboole_0)
    | ~ v2_funct_1(k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_relat_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_103]),c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( k1_relat_1(X1) = u1_struct_0(esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_119,c_0_114])).

cnf(c_0_123,plain,
    ( k2_relat_1(X1) = k2_relat_1(k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_108])).

cnf(c_0_124,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk4_0
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_58])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(k2_funct_1(u1_struct_0(esk2_0)),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_funct_2(u1_struct_0(esk2_0),X1,k1_xboole_0)
    | ~ v2_funct_1(u1_struct_0(esk2_0))
    | ~ v1_funct_1(u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_76])])).

cnf(c_0_127,negated_conjecture,
    ( v2_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_122])).

cnf(c_0_129,plain,
    ( k2_relat_1(k2_relat_1(X1)) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_123])).

cnf(c_0_130,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk4_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_110]),c_0_110]),c_0_110]),c_0_110]),c_0_110])]),c_0_127]),c_0_128]),c_0_122]),c_0_76])])).

cnf(c_0_132,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_110]),c_0_122])).

cnf(c_0_133,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_113]),c_0_107]),c_0_114])])).

cnf(c_0_134,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_110]),c_0_114])])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_136,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_103,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( k7_relset_1(k1_xboole_0,u1_struct_0(esk1_0),k2_funct_1(k1_xboole_0),k1_xboole_0) != k8_relset_1(u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_110]),c_0_110]),c_0_122]),c_0_134]),c_0_122]),c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_135]),c_0_136])])).

cnf(c_0_139,negated_conjecture,
    ( k7_relset_1(k1_xboole_0,u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0) != k8_relset_1(u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_140,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_141,plain,
    ( k2_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_133]),c_0_133])).

cnf(c_0_142,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_141]),c_0_86]),c_0_76])])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_93]),c_0_133]),c_0_97]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.96/1.13  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.96/1.13  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.96/1.13  #
% 0.96/1.13  # Preprocessing time       : 0.029 s
% 0.96/1.13  # Presaturation interreduction done
% 0.96/1.13  
% 0.96/1.13  # Proof found!
% 0.96/1.13  # SZS status Theorem
% 0.96/1.13  # SZS output start CNFRefutation
% 0.96/1.13  fof(t68_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_2)).
% 0.96/1.13  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.96/1.13  fof(t67_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 0.96/1.13  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 0.96/1.13  fof(t63_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 0.96/1.13  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 0.96/1.13  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.96/1.13  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.96/1.13  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.96/1.13  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.96/1.13  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.96/1.13  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.96/1.13  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.96/1.13  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.96/1.13  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.96/1.13  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.96/1.13  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.96/1.13  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.96/1.13  fof(t48_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 0.96/1.13  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.96/1.13  fof(c_0_20, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4))))))), inference(assume_negation,[status(cth)],[t68_tops_2])).
% 0.96/1.13  fof(c_0_21, negated_conjecture, (l1_struct_0(esk1_0)&(l1_struct_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)&v2_funct_1(esk3_0))&k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.96/1.13  fof(c_0_22, plain, ![X39]:(~l1_struct_0(X39)|k2_struct_0(X39)=u1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.96/1.13  fof(c_0_23, plain, ![X49, X50, X51, X52]:(~l1_struct_0(X49)|(~l1_struct_0(X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X50))))|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X49)))|(k2_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51)!=k2_struct_0(X50)|~v2_funct_1(X51)|k7_relset_1(u1_struct_0(X49),u1_struct_0(X50),X51,X52)=k8_relset_1(u1_struct_0(X50),u1_struct_0(X49),k2_tops_2(u1_struct_0(X49),u1_struct_0(X50),X51),X52)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_tops_2])])])).
% 0.96/1.13  fof(c_0_24, plain, ![X40, X41, X42]:(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|(k2_relset_1(X40,X41,X42)!=X41|~v2_funct_1(X42)|k2_tops_2(X40,X41,X42)=k2_funct_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.96/1.13  fof(c_0_25, plain, ![X46, X47, X48]:(~l1_struct_0(X46)|(~l1_struct_0(X47)|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X47))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X47))))|(k2_relset_1(u1_struct_0(X46),u1_struct_0(X47),X48)!=k2_struct_0(X47)|~v2_funct_1(X48)|v2_funct_1(k2_tops_2(u1_struct_0(X46),u1_struct_0(X47),X48)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_tops_2])])])).
% 0.96/1.13  cnf(c_0_26, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_27, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.96/1.13  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_29, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X4)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.96/1.13  cnf(c_0_30, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.96/1.13  fof(c_0_31, plain, ![X14]:(~v1_relat_1(X14)|~v1_funct_1(X14)|(~v2_funct_1(X14)|k2_funct_1(k2_funct_1(X14))=X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.96/1.13  cnf(c_0_32, plain, (v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.96/1.13  cnf(c_0_33, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.96/1.13  fof(c_0_34, plain, ![X33, X34, X35]:(((v1_funct_1(k2_funct_1(X35))|(~v2_funct_1(X35)|k2_relset_1(X33,X34,X35)!=X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&(v1_funct_2(k2_funct_1(X35),X34,X33)|(~v2_funct_1(X35)|k2_relset_1(X33,X34,X35)!=X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))))&(m1_subset_1(k2_funct_1(X35),k1_zfmisc_1(k2_zfmisc_1(X34,X33)))|(~v2_funct_1(X35)|k2_relset_1(X33,X34,X35)!=X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.96/1.13  fof(c_0_35, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.96/1.13  cnf(c_0_36, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_38, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_41, plain, (k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3),X4)=k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=u1_struct_0(X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v2_funct_1(X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.96/1.13  cnf(c_0_42, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.96/1.13  cnf(c_0_43, plain, (v2_funct_1(k2_funct_1(X1))|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=u1_struct_0(X3)|~l1_struct_0(X3)|~l1_struct_0(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.96/1.13  cnf(c_0_44, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_26, c_0_33])).
% 0.96/1.13  cnf(c_0_45, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_46, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.96/1.13  cnf(c_0_47, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.96/1.13  fof(c_0_48, plain, ![X13]:((k2_relat_1(X13)=k1_relat_1(k2_funct_1(X13))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_relat_1(X13)=k2_relat_1(k2_funct_1(X13))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.96/1.13  fof(c_0_49, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k2_relset_1(X27,X28,X29)=k2_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.96/1.13  fof(c_0_50, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|m1_subset_1(k2_relset_1(X21,X22,X23),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.96/1.13  fof(c_0_51, plain, ![X10]:m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.96/1.13  fof(c_0_52, plain, ![X9]:k2_subset_1(X9)=X9, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.96/1.13  cnf(c_0_53, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0),esk4_0)!=k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_30]), c_0_33]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.96/1.13  cnf(c_0_54, plain, (k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3),X4)=k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,X4)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3))!=k2_struct_0(X2)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_funct_1(X3))!=u1_struct_0(X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~v1_funct_2(k2_funct_1(X3),u1_struct_0(X1),u1_struct_0(X2))|~v2_funct_1(k2_funct_1(X3))|~v2_funct_1(X3)|~v1_funct_1(k2_funct_1(X3))|~v1_funct_1(X3)|~v1_relat_1(X3)|~m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.96/1.13  cnf(c_0_55, negated_conjecture, (v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_33]), c_0_44]), c_0_33]), c_0_28]), c_0_45]), c_0_37]), c_0_38]), c_0_39])])).
% 0.96/1.13  cnf(c_0_56, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_33]), c_0_37]), c_0_38]), c_0_39])])).
% 0.96/1.13  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_40])).
% 0.96/1.13  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.96/1.13  cnf(c_0_59, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.96/1.13  cnf(c_0_60, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.96/1.13  fof(c_0_61, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.96/1.13  fof(c_0_62, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.96/1.13  cnf(c_0_63, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.96/1.13  cnf(c_0_64, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.96/1.13  cnf(c_0_65, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.96/1.13  fof(c_0_66, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.96/1.13  fof(c_0_67, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|m1_subset_1(k1_relset_1(X18,X19,X20),k1_zfmisc_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.96/1.13  fof(c_0_68, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k1_relset_1(X24,X25,X26)=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.96/1.13  cnf(c_0_69, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_45]), c_0_28]), c_0_55]), c_0_38]), c_0_56]), c_0_39]), c_0_57]), c_0_58])])).
% 0.96/1.13  cnf(c_0_70, plain, (k2_relset_1(X1,X2,k2_funct_1(X3))=k1_relat_1(X3)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X3)|~m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.96/1.13  fof(c_0_71, plain, ![X36, X37, X38]:((X37=k1_xboole_0|k8_relset_1(X36,X37,X38,X37)=X36|(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(X36!=k1_xboole_0|k8_relset_1(X36,X37,X38,X37)=X36|(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).
% 0.96/1.13  fof(c_0_72, plain, ![X30, X31, X32]:((k7_relset_1(X30,X31,X32,X30)=k2_relset_1(X30,X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(k8_relset_1(X30,X31,X32,X31)=k1_relset_1(X30,X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.96/1.13  cnf(c_0_73, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.96/1.13  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.96/1.13  cnf(c_0_75, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_63, c_0_60])).
% 0.96/1.13  cnf(c_0_76, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.96/1.13  cnf(c_0_77, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.96/1.13  cnf(c_0_78, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.96/1.13  cnf(c_0_79, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.96/1.13  cnf(c_0_80, negated_conjecture, (k1_relat_1(esk3_0)!=k2_struct_0(esk1_0)|k1_relat_1(esk3_0)!=u1_struct_0(esk1_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_38]), c_0_39]), c_0_57])])).
% 0.96/1.13  cnf(c_0_81, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.96/1.13  cnf(c_0_82, plain, (X1=k1_xboole_0|k8_relset_1(X2,X1,X3,X1)=X2|~v1_funct_1(X3)|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.96/1.13  cnf(c_0_83, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.96/1.13  cnf(c_0_84, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.96/1.13  cnf(c_0_85, plain, (m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.96/1.13  cnf(c_0_86, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_77])).
% 0.96/1.13  cnf(c_0_87, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.96/1.13  cnf(c_0_88, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.96/1.13  cnf(c_0_89, plain, (k2_relset_1(X1,X2,X3)=k2_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_60, c_0_60])).
% 0.96/1.13  cnf(c_0_90, negated_conjecture, (k1_relat_1(esk3_0)!=k2_struct_0(esk1_0)|k1_relat_1(esk3_0)!=u1_struct_0(esk1_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_33]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.96/1.13  cnf(c_0_91, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.96/1.13  cnf(c_0_92, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk2_0))=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_40]), c_0_37]), c_0_39])])).
% 0.96/1.13  cnf(c_0_93, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relat_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_79, c_0_83])).
% 0.96/1.13  cnf(c_0_94, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_84, c_0_74])).
% 0.96/1.13  cnf(c_0_95, plain, (m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.96/1.13  cnf(c_0_96, plain, (m1_subset_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_87, c_0_76])).
% 0.96/1.13  cnf(c_0_97, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_88])).
% 0.96/1.13  cnf(c_0_98, negated_conjecture, (k2_relset_1(X1,X2,esk3_0)=u1_struct_0(esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_89]), c_0_40])])).
% 0.96/1.13  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk3_0)!=k2_struct_0(esk1_0)|k1_relat_1(esk3_0)!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_33]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.96/1.13  cnf(c_0_100, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_40])])).
% 0.96/1.13  cnf(c_0_101, plain, (X1=k2_relat_1(k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.96/1.13  cnf(c_0_102, plain, (m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_95])).
% 0.96/1.13  cnf(c_0_103, plain, (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.96/1.13  cnf(c_0_104, negated_conjecture, (k2_relat_1(esk3_0)=u1_struct_0(esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_60, c_0_98])).
% 0.96/1.13  cnf(c_0_105, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|k2_struct_0(esk1_0)!=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.96/1.13  cnf(c_0_106, plain, (k2_relat_1(k2_relat_1(k1_xboole_0))=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.96/1.13  cnf(c_0_107, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_101, c_0_103])).
% 0.96/1.13  cnf(c_0_108, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_75, c_0_86])).
% 0.96/1.13  cnf(c_0_109, negated_conjecture, (k2_relat_1(esk3_0)=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_104, c_0_40])).
% 0.96/1.13  cnf(c_0_110, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_27]), c_0_45])])).
% 0.96/1.13  cnf(c_0_111, plain, (k2_relat_1(k1_relat_1(k1_xboole_0))=k1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107]), c_0_107])).
% 0.96/1.13  cnf(c_0_112, plain, (X1=k2_relat_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(X2)))|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_94, c_0_108])).
% 0.96/1.13  cnf(c_0_113, negated_conjecture, (k2_relat_1(esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_109, c_0_110])).
% 0.96/1.13  cnf(c_0_114, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_110]), c_0_97])).
% 0.96/1.13  cnf(c_0_115, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k1_xboole_0))|k2_relset_1(X2,k1_xboole_0,X1)!=k1_xboole_0|~v1_funct_2(X1,X2,k1_xboole_0)|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_86]), c_0_97])).
% 0.96/1.13  cnf(c_0_116, plain, (k2_relset_1(X1,X2,k1_relat_1(k1_xboole_0))=k1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_111]), c_0_103])])).
% 0.96/1.13  cnf(c_0_117, negated_conjecture, (X1=u1_struct_0(esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_112, c_0_109])).
% 0.96/1.13  cnf(c_0_118, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_87, c_0_97])).
% 0.96/1.13  cnf(c_0_119, negated_conjecture, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])])).
% 0.96/1.13  cnf(c_0_120, plain, (m1_subset_1(k2_funct_1(k1_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))|k1_relat_1(k1_xboole_0)!=k1_xboole_0|~v1_funct_2(k1_relat_1(k1_xboole_0),X1,k1_xboole_0)|~v2_funct_1(k1_relat_1(k1_xboole_0))|~v1_funct_1(k1_relat_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_103]), c_0_116])).
% 0.96/1.13  cnf(c_0_121, negated_conjecture, (k1_relat_1(X1)=u1_struct_0(esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.96/1.13  cnf(c_0_122, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_119, c_0_114])).
% 0.96/1.13  cnf(c_0_123, plain, (k2_relat_1(X1)=k2_relat_1(k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_101, c_0_108])).
% 0.96/1.13  cnf(c_0_124, negated_conjecture, (u1_struct_0(esk2_0)=esk4_0|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_94, c_0_58])).
% 0.96/1.13  cnf(c_0_125, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.96/1.13  cnf(c_0_126, negated_conjecture, (m1_subset_1(k2_funct_1(u1_struct_0(esk2_0)),k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_funct_2(u1_struct_0(esk2_0),X1,k1_xboole_0)|~v2_funct_1(u1_struct_0(esk2_0))|~v1_funct_1(u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_76])])).
% 0.96/1.13  cnf(c_0_127, negated_conjecture, (v2_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_38, c_0_122])).
% 0.96/1.13  cnf(c_0_128, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_39, c_0_122])).
% 0.96/1.13  cnf(c_0_129, plain, (k2_relat_1(k2_relat_1(X1))=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_106, c_0_123])).
% 0.96/1.13  cnf(c_0_130, negated_conjecture, (u1_struct_0(esk2_0)=esk4_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 0.96/1.13  cnf(c_0_131, negated_conjecture, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|~v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_110]), c_0_110]), c_0_110]), c_0_110]), c_0_110])]), c_0_127]), c_0_128]), c_0_122]), c_0_76])])).
% 0.96/1.13  cnf(c_0_132, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_110]), c_0_122])).
% 0.96/1.13  cnf(c_0_133, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_113]), c_0_107]), c_0_114])])).
% 0.96/1.13  cnf(c_0_134, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_110]), c_0_114])])).
% 0.96/1.13  cnf(c_0_135, negated_conjecture, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.96/1.13  cnf(c_0_136, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_103, c_0_133])).
% 0.96/1.13  cnf(c_0_137, negated_conjecture, (k7_relset_1(k1_xboole_0,u1_struct_0(esk1_0),k2_funct_1(k1_xboole_0),k1_xboole_0)!=k8_relset_1(u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_110]), c_0_110]), c_0_122]), c_0_134]), c_0_122]), c_0_134])).
% 0.96/1.13  cnf(c_0_138, negated_conjecture, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_135]), c_0_136])])).
% 0.96/1.13  cnf(c_0_139, negated_conjecture, (k7_relset_1(k1_xboole_0,u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0)!=k8_relset_1(u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_137, c_0_138])).
% 0.96/1.13  cnf(c_0_140, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.96/1.13  cnf(c_0_141, plain, (k2_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_133]), c_0_133])).
% 0.96/1.13  cnf(c_0_142, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),k1_xboole_0,k1_xboole_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_141]), c_0_86]), c_0_76])])).
% 0.96/1.13  cnf(c_0_143, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_93]), c_0_133]), c_0_97]), c_0_76])]), ['proof']).
% 0.96/1.13  # SZS output end CNFRefutation
% 0.96/1.13  # Proof object total steps             : 144
% 0.96/1.13  # Proof object clause steps            : 103
% 0.96/1.13  # Proof object formula steps           : 41
% 0.96/1.13  # Proof object conjectures             : 51
% 0.96/1.13  # Proof object clause conjectures      : 48
% 0.96/1.13  # Proof object formula conjectures     : 3
% 0.96/1.13  # Proof object initial clauses used    : 32
% 0.96/1.13  # Proof object initial formulas used   : 20
% 0.96/1.13  # Proof object generating inferences   : 55
% 0.96/1.13  # Proof object simplifying inferences  : 114
% 0.96/1.13  # Training examples: 0 positive, 0 negative
% 0.96/1.13  # Parsed axioms                        : 21
% 0.96/1.13  # Removed by relevancy pruning/SinE    : 0
% 0.96/1.13  # Initial clauses                      : 41
% 0.96/1.13  # Removed in clause preprocessing      : 1
% 0.96/1.13  # Initial clauses in saturation        : 40
% 0.96/1.13  # Processed clauses                    : 8375
% 0.96/1.13  # ...of these trivial                  : 53
% 0.96/1.13  # ...subsumed                          : 7037
% 0.96/1.13  # ...remaining for further processing  : 1285
% 0.96/1.13  # Other redundant clauses eliminated   : 1273
% 0.96/1.13  # Clauses deleted for lack of memory   : 0
% 0.96/1.13  # Backward-subsumed                    : 70
% 0.96/1.13  # Backward-rewritten                   : 664
% 0.96/1.13  # Generated clauses                    : 62767
% 0.96/1.13  # ...of the previous two non-trivial   : 56129
% 0.96/1.13  # Contextual simplify-reflections      : 56
% 0.96/1.13  # Paramodulations                      : 61494
% 0.96/1.13  # Factorizations                       : 0
% 0.96/1.13  # Equation resolutions                 : 1273
% 0.96/1.13  # Propositional unsat checks           : 0
% 0.96/1.13  #    Propositional check models        : 0
% 0.96/1.13  #    Propositional check unsatisfiable : 0
% 0.96/1.13  #    Propositional clauses             : 0
% 0.96/1.13  #    Propositional clauses after purity: 0
% 0.96/1.13  #    Propositional unsat core size     : 0
% 0.96/1.13  #    Propositional preprocessing time  : 0.000
% 0.96/1.13  #    Propositional encoding time       : 0.000
% 0.96/1.13  #    Propositional solver time         : 0.000
% 0.96/1.13  #    Success case prop preproc time    : 0.000
% 0.96/1.13  #    Success case prop encoding time   : 0.000
% 0.96/1.13  #    Success case prop solver time     : 0.000
% 0.96/1.13  # Current number of processed clauses  : 503
% 0.96/1.13  #    Positive orientable unit clauses  : 34
% 0.96/1.13  #    Positive unorientable unit clauses: 0
% 0.96/1.13  #    Negative unit clauses             : 5
% 0.96/1.13  #    Non-unit-clauses                  : 464
% 0.96/1.13  # Current number of unprocessed clauses: 47330
% 0.96/1.13  # ...number of literals in the above   : 241857
% 0.96/1.13  # Current number of archived formulas  : 0
% 0.96/1.13  # Current number of archived clauses   : 774
% 0.96/1.13  # Clause-clause subsumption calls (NU) : 918683
% 0.96/1.13  # Rec. Clause-clause subsumption calls : 553650
% 0.96/1.13  # Non-unit clause-clause subsumptions  : 7160
% 0.96/1.13  # Unit Clause-clause subsumption calls : 1728
% 0.96/1.13  # Rewrite failures with RHS unbound    : 0
% 0.96/1.13  # BW rewrite match attempts            : 197
% 0.96/1.13  # BW rewrite match successes           : 23
% 0.96/1.13  # Condensation attempts                : 0
% 0.96/1.13  # Condensation successes               : 0
% 0.96/1.13  # Termbank termtop insertions          : 1173011
% 0.96/1.13  
% 0.96/1.13  # -------------------------------------------------
% 0.96/1.13  # User time                : 0.765 s
% 0.96/1.13  # System time              : 0.027 s
% 0.96/1.13  # Total time               : 0.792 s
% 0.96/1.13  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

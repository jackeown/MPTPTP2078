%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 712 expanded)
%              Number of clauses        :   80 ( 249 expanded)
%              Number of leaves         :   21 ( 177 expanded)
%              Depth                    :   21
%              Number of atoms          :  478 (6603 expanded)
%              Number of equality atoms :   81 (1219 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_struct_0(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                          & v2_funct_1(X4)
                          & k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5) = k2_struct_0(X2)
                          & k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5) = k2_struct_0(X3)
                          & v2_funct_1(X5) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X3),k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X4,X5)),k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X2),u1_struct_0(X3),X5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tops_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

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

fof(t66_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X2) )
           => k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t199_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k2_relat_1(X1) = k2_relat_1(X2)
               => k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(fc8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v1_xboole_0(X2)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X2,X3)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k5_relat_1(X4,X5))
        & v1_funct_2(k5_relat_1(X4,X5),X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_2)).

fof(t46_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X2) )
           => v2_funct_1(k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & l1_struct_0(X3) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                       => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4) = k2_struct_0(X2)
                            & v2_funct_1(X4)
                            & k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5) = k2_struct_0(X2)
                            & k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5) = k2_struct_0(X3)
                            & v2_funct_1(X5) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X3),k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X4,X5)),k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X2),u1_struct_0(X3),X5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t66_tops_2])).

fof(c_0_22,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk4_0)
    & k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0) = k2_struct_0(esk2_0)
    & k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0) = k2_struct_0(esk3_0)
    & v2_funct_1(esk5_0)
    & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_24,plain,(
    ! [X59] :
      ( ~ l1_struct_0(X59)
      | k2_struct_0(X59) = u1_struct_0(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_25,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | ~ v1_funct_1(X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_partfun1(X46,X47,X48,X49,X50,X51) = k5_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_29,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_struct_0(esk2_0) = k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0) = k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_38,plain,(
    ! [X61,X62,X63] :
      ( ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,X61,X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | k2_relset_1(X61,X62,X63) != X62
      | ~ v2_funct_1(X63)
      | k2_tops_2(X61,X62,X63) = k2_funct_1(X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk4_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_40,negated_conjecture,
    ( k2_struct_0(esk3_0) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_33]),c_0_27])])).

cnf(c_0_43,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_30]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(esk5_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_41])])).

fof(c_0_48,plain,(
    ! [X56,X57,X58] :
      ( ( v1_funct_1(k2_funct_1(X58))
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_2(k2_funct_1(X58),X57,X56)
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( m1_subset_1(k2_funct_1(X58),k1_zfmisc_1(k2_zfmisc_1(X57,X56)))
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_funct_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_37]),c_0_27])])).

cnf(c_0_50,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_40]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_55,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk5_0),k2_funct_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_43]),c_0_50]),c_0_51]),c_0_52]),c_0_36]),c_0_33])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_27]),c_0_44]),c_0_45]),c_0_46]),c_0_37])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_33]),c_0_50]),c_0_51]),c_0_52]),c_0_36])])).

fof(c_0_59,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ v2_funct_1(X24)
      | ~ v2_funct_1(X25)
      | k2_funct_1(k5_relat_1(X24,X25)) = k5_relat_1(k2_funct_1(X25),k2_funct_1(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).

cnf(c_0_60,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_62,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k1_relset_1(X26,X27,X28) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_63,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k5_relat_1(k2_funct_1(esk5_0),k2_funct_1(esk4_0)))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_35]),c_0_57]),c_0_58])])).

cnf(c_0_65,plain,
    ( k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_33]),c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_61])])).

fof(c_0_68,plain,(
    ! [X52,X53,X54,X55] :
      ( ( ~ r2_funct_2(X52,X53,X54,X55)
        | X54 = X55
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != X55
        | r2_funct_2(X52,X53,X54,X55)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

fof(c_0_69,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k2_relat_1(X13) != k2_relat_1(X14)
      | k2_relat_1(k5_relat_1(X13,X15)) = k2_relat_1(k5_relat_1(X14,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).

fof(c_0_70,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k7_relat_1(X18,X17) = k5_relat_1(k6_relat_1(X17),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_71,plain,(
    ! [X16] :
      ( k1_relat_1(k6_relat_1(X16)) = X16
      & k2_relat_1(k6_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_72,plain,(
    ! [X21] :
      ( v1_relat_1(k6_relat_1(X21))
      & v4_relat_1(k6_relat_1(X21),X21)
      & v5_relat_1(k6_relat_1(X21),X21) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

fof(c_0_73,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_tarski(k1_relat_1(X20),X19)
      | k7_relat_1(X20,X19) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_74,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_30]),c_0_39])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k2_funct_1(k5_relat_1(esk4_0,esk5_0)))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_52]),c_0_46]),c_0_36]),c_0_37]),c_0_66]),c_0_67])])).

cnf(c_0_77,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X1) != k2_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_33])])).

fof(c_0_84,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_85,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( v1_funct_1(k1_partfun1(X35,X36,X37,X38,X39,X40))
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( m1_subset_1(k1_partfun1(X35,X36,X37,X38,X39,X40),k1_zfmisc_1(k2_zfmisc_1(X35,X38)))
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_86,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)) != u1_struct_0(esk3_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_funct_1(k5_relat_1(esk4_0,esk5_0)),k2_funct_1(k5_relat_1(esk4_0,esk5_0)))
    | ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_43])).

cnf(c_0_87,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_88,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_89,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_90,plain,
    ( k2_relat_1(k7_relat_1(X1,k2_relat_1(X2))) = k2_relat_1(k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81])])])).

cnf(c_0_91,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = esk5_0
    | ~ r1_tarski(u1_struct_0(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_66])])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)) != u1_struct_0(esk3_0)
    | ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_53]),c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,esk5_0)) = u1_struct_0(esk3_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(u1_struct_0(esk2_0),k2_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_47]),c_0_66])])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_97,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_35])).

fof(c_0_98,plain,(
    ! [X41,X42,X43,X44,X45] :
      ( ( v1_funct_1(k5_relat_1(X44,X45))
        | v1_xboole_0(X42)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X41,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X42,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( v1_funct_2(k5_relat_1(X44,X45),X41,X43)
        | v1_xboole_0(X42)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X41,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X42,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).

cnf(c_0_99,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,esk5_0)) != u1_struct_0(esk3_0)
    | ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_26])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,esk5_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_39]),c_0_67]),c_0_96])])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_33]),c_0_36])])).

cnf(c_0_102,plain,
    ( v1_funct_2(k5_relat_1(X1,X2),X3,X4)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ v1_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_27]),c_0_37])])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(k5_relat_1(X1,esk5_0),X2,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_33]),c_0_51]),c_0_36])])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_27]),c_0_45]),c_0_37])])).

cnf(c_0_108,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_109,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_110,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_35])).

cnf(c_0_111,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_88]),c_0_44]),c_0_45]),c_0_46]),c_0_37]),c_0_27])])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk3_0))))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_33]),c_0_36])])).

cnf(c_0_113,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_88]),c_0_50]),c_0_51]),c_0_52]),c_0_36]),c_0_33])])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_27]),c_0_37])])).

fof(c_0_115,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v2_funct_1(X22)
      | ~ v2_funct_1(X23)
      | v2_funct_1(k5_relat_1(X22,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_funct_1])])])).

fof(c_0_116,plain,(
    ! [X60] :
      ( v2_struct_0(X60)
      | ~ l1_struct_0(X60)
      | ~ v1_xboole_0(u1_struct_0(X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_117,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])])).

cnf(c_0_118,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_119,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_52]),c_0_46]),c_0_36]),c_0_37]),c_0_66]),c_0_67])])).

cnf(c_0_121,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_31])]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:24:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.54  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.54  #
% 0.19/0.54  # Preprocessing time       : 0.029 s
% 0.19/0.54  # Presaturation interreduction done
% 0.19/0.54  
% 0.19/0.54  # Proof found!
% 0.19/0.54  # SZS status Theorem
% 0.19/0.54  # SZS output start CNFRefutation
% 0.19/0.54  fof(t66_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:((~(v2_struct_0(X3))&l1_struct_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>(((((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)=k2_struct_0(X2)&v2_funct_1(X4))&k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5)=k2_struct_0(X2))&k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5)=k2_struct_0(X3))&v2_funct_1(X5))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X3),k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X4,X5)),k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X2),u1_struct_0(X3),X5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tops_2)).
% 0.19/0.54  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.54  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.54  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.54  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 0.19/0.54  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.54  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.54  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.54  fof(t66_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 0.19/0.54  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.54  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.19/0.54  fof(t199_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k2_relat_1(X1)=k2_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 0.19/0.54  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.54  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.54  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.19/0.54  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.54  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.54  fof(fc8_funct_2, axiom, ![X1, X2, X3, X4, X5]:(((((((~(v1_xboole_0(X2))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X5))&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v1_funct_1(k5_relat_1(X4,X5))&v1_funct_2(k5_relat_1(X4,X5),X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_2)).
% 0.19/0.54  fof(t46_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>v2_funct_1(k5_relat_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_1)).
% 0.19/0.54  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.54  fof(c_0_21, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:((~(v2_struct_0(X3))&l1_struct_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>(((((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X4)=k2_struct_0(X2)&v2_funct_1(X4))&k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5)=k2_struct_0(X2))&k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X5)=k2_struct_0(X3))&v2_funct_1(X5))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X3),k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X4,X5)),k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X2),u1_struct_0(X3),X5),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X4)))))))))), inference(assume_negation,[status(cth)],[t66_tops_2])).
% 0.19/0.54  fof(c_0_22, negated_conjecture, (l1_struct_0(esk1_0)&((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((((k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0)=k2_struct_0(esk2_0)&v2_funct_1(esk4_0))&k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0)=k2_struct_0(esk2_0))&k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0)=k2_struct_0(esk3_0))&v2_funct_1(esk5_0))&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.19/0.54  fof(c_0_23, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.54  fof(c_0_24, plain, ![X59]:(~l1_struct_0(X59)|k2_struct_0(X59)=u1_struct_0(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.54  cnf(c_0_25, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_26, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.54  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  fof(c_0_28, plain, ![X46, X47, X48, X49, X50, X51]:(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k1_partfun1(X46,X47,X48,X49,X50,X51)=k5_relat_1(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.54  cnf(c_0_29, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.54  cnf(c_0_30, negated_conjecture, (k2_struct_0(esk2_0)=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.19/0.54  cnf(c_0_31, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_32, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0)=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_34, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_35, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.54  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  fof(c_0_38, plain, ![X61, X62, X63]:(~v1_funct_1(X63)|~v1_funct_2(X63,X61,X62)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))|(k2_relset_1(X61,X62,X63)!=X62|~v2_funct_1(X63)|k2_tops_2(X61,X62,X63)=k2_funct_1(X63))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.19/0.54  cnf(c_0_39, negated_conjecture, (k2_relat_1(esk4_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.19/0.54  cnf(c_0_40, negated_conjecture, (k2_struct_0(esk3_0)=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_33])])).
% 0.19/0.54  cnf(c_0_41, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_42, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_33]), c_0_27])])).
% 0.19/0.54  cnf(c_0_43, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.54  cnf(c_0_44, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0)=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_30]), c_0_39])).
% 0.19/0.54  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_46, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_47, negated_conjecture, (k2_relat_1(esk5_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_41])])).
% 0.19/0.54  fof(c_0_48, plain, ![X56, X57, X58]:(((v1_funct_1(k2_funct_1(X58))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(v1_funct_2(k2_funct_1(X58),X57,X56)|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&(m1_subset_1(k2_funct_1(X58),k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.54  cnf(c_0_49, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0),k2_funct_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_37]), c_0_27])])).
% 0.19/0.54  cnf(c_0_50, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0)=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_40]), c_0_47])).
% 0.19/0.54  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_52, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_53, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.54  fof(c_0_54, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.54  fof(c_0_55, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.54  cnf(c_0_56, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk5_0),k2_funct_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_43]), c_0_50]), c_0_51]), c_0_52]), c_0_36]), c_0_33])])).
% 0.19/0.54  cnf(c_0_57, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_27]), c_0_44]), c_0_45]), c_0_46]), c_0_37])])).
% 0.19/0.54  cnf(c_0_58, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_33]), c_0_50]), c_0_51]), c_0_52]), c_0_36])])).
% 0.19/0.54  fof(c_0_59, plain, ![X24, X25]:(~v1_relat_1(X24)|~v1_funct_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)|(~v2_funct_1(X24)|~v2_funct_1(X25)|k2_funct_1(k5_relat_1(X24,X25))=k5_relat_1(k2_funct_1(X25),k2_funct_1(X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).
% 0.19/0.54  cnf(c_0_60, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.54  cnf(c_0_61, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.54  fof(c_0_62, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k1_relset_1(X26,X27,X28)=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.54  cnf(c_0_63, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_64, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k5_relat_1(k2_funct_1(esk5_0),k2_funct_1(esk4_0)))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_35]), c_0_57]), c_0_58])])).
% 0.19/0.54  cnf(c_0_65, plain, (k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.54  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_33]), c_0_61])])).
% 0.19/0.54  cnf(c_0_67, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_27]), c_0_61])])).
% 0.19/0.54  fof(c_0_68, plain, ![X52, X53, X54, X55]:((~r2_funct_2(X52,X53,X54,X55)|X54=X55|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&(X54!=X55|r2_funct_2(X52,X53,X54,X55)|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.19/0.54  fof(c_0_69, plain, ![X13, X14, X15]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|(~v1_relat_1(X15)|(k2_relat_1(X13)!=k2_relat_1(X14)|k2_relat_1(k5_relat_1(X13,X15))=k2_relat_1(k5_relat_1(X14,X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).
% 0.19/0.54  fof(c_0_70, plain, ![X17, X18]:(~v1_relat_1(X18)|k7_relat_1(X18,X17)=k5_relat_1(k6_relat_1(X17),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.54  fof(c_0_71, plain, ![X16]:(k1_relat_1(k6_relat_1(X16))=X16&k2_relat_1(k6_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.54  fof(c_0_72, plain, ![X21]:((v1_relat_1(k6_relat_1(X21))&v4_relat_1(k6_relat_1(X21),X21))&v5_relat_1(k6_relat_1(X21),X21)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.19/0.54  fof(c_0_73, plain, ![X19, X20]:(~v1_relat_1(X20)|(~r1_tarski(k1_relat_1(X20),X19)|k7_relat_1(X20,X19)=X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.54  cnf(c_0_74, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.54  cnf(c_0_75, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0)=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_30]), c_0_39])).
% 0.19/0.54  cnf(c_0_76, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0)),k2_funct_1(k5_relat_1(esk4_0,esk5_0)))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_52]), c_0_46]), c_0_36]), c_0_37]), c_0_66]), c_0_67])])).
% 0.19/0.54  cnf(c_0_77, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.54  cnf(c_0_78, plain, (k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k2_relat_1(X1)!=k2_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.54  cnf(c_0_79, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.54  cnf(c_0_80, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.54  cnf(c_0_81, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.54  cnf(c_0_82, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.54  cnf(c_0_83, negated_conjecture, (k1_relat_1(esk5_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_33])])).
% 0.19/0.54  fof(c_0_84, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.54  fof(c_0_85, plain, ![X35, X36, X37, X38, X39, X40]:((v1_funct_1(k1_partfun1(X35,X36,X37,X38,X39,X40))|(~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(m1_subset_1(k1_partfun1(X35,X36,X37,X38,X39,X40),k1_zfmisc_1(k2_zfmisc_1(X35,X38)))|(~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.54  cnf(c_0_86, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0))!=u1_struct_0(esk3_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_funct_1(k5_relat_1(esk4_0,esk5_0)),k2_funct_1(k5_relat_1(esk4_0,esk5_0)))|~v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~v1_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_76, c_0_43])).
% 0.19/0.54  cnf(c_0_87, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_77])).
% 0.19/0.54  cnf(c_0_88, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.54  cnf(c_0_89, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.54  cnf(c_0_90, plain, (k2_relat_1(k7_relat_1(X1,k2_relat_1(X2)))=k2_relat_1(k5_relat_1(X2,X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81])])])).
% 0.19/0.54  cnf(c_0_91, negated_conjecture, (k7_relat_1(esk5_0,X1)=esk5_0|~r1_tarski(u1_struct_0(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_66])])).
% 0.19/0.54  cnf(c_0_92, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.54  cnf(c_0_93, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.54  cnf(c_0_94, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),k5_relat_1(esk4_0,esk5_0))!=u1_struct_0(esk3_0)|~v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~v1_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_53]), c_0_89])).
% 0.19/0.54  cnf(c_0_95, negated_conjecture, (k2_relat_1(k5_relat_1(X1,esk5_0))=u1_struct_0(esk3_0)|~v1_relat_1(X1)|~r1_tarski(u1_struct_0(esk2_0),k2_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_47]), c_0_66])])).
% 0.19/0.54  cnf(c_0_96, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_92])).
% 0.19/0.54  cnf(c_0_97, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_93, c_0_35])).
% 0.19/0.54  fof(c_0_98, plain, ![X41, X42, X43, X44, X45]:((v1_funct_1(k5_relat_1(X44,X45))|(v1_xboole_0(X42)|~v1_funct_1(X44)|~v1_funct_2(X44,X41,X42)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~v1_funct_1(X45)|~v1_funct_2(X45,X42,X43)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&(v1_funct_2(k5_relat_1(X44,X45),X41,X43)|(v1_xboole_0(X42)|~v1_funct_1(X44)|~v1_funct_2(X44,X41,X42)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~v1_funct_1(X45)|~v1_funct_2(X45,X42,X43)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).
% 0.19/0.54  cnf(c_0_99, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,esk5_0))!=u1_struct_0(esk3_0)|~v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~v1_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_94, c_0_26])).
% 0.19/0.54  cnf(c_0_100, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,esk5_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_39]), c_0_67]), c_0_96])])).
% 0.19/0.54  cnf(c_0_101, negated_conjecture, (v1_funct_1(k5_relat_1(X1,esk5_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_33]), c_0_36])])).
% 0.19/0.54  cnf(c_0_102, plain, (v1_funct_2(k5_relat_1(X1,X2),X3,X4)|v1_xboole_0(X5)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.54  cnf(c_0_103, negated_conjecture, (~v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~v1_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.19/0.54  cnf(c_0_104, negated_conjecture, (v1_funct_1(k5_relat_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_27]), c_0_37])])).
% 0.19/0.54  cnf(c_0_105, negated_conjecture, (v1_funct_2(k5_relat_1(X1,esk5_0),X2,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~v1_funct_2(X1,X2,u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_33]), c_0_51]), c_0_36])])).
% 0.19/0.54  cnf(c_0_106, negated_conjecture, (~v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 0.19/0.54  cnf(c_0_107, negated_conjecture, (v1_funct_2(k5_relat_1(esk4_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_27]), c_0_45]), c_0_37])])).
% 0.19/0.54  cnf(c_0_108, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.54  cnf(c_0_109, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.19/0.54  cnf(c_0_110, plain, (m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))), inference(spm,[status(thm)],[c_0_108, c_0_35])).
% 0.19/0.54  cnf(c_0_111, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_88]), c_0_44]), c_0_45]), c_0_46]), c_0_37]), c_0_27])])).
% 0.19/0.54  cnf(c_0_112, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk3_0))))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_33]), c_0_36])])).
% 0.19/0.54  cnf(c_0_113, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_88]), c_0_50]), c_0_51]), c_0_52]), c_0_36]), c_0_33])])).
% 0.19/0.54  cnf(c_0_114, negated_conjecture, (m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_27]), c_0_37])])).
% 0.19/0.54  fof(c_0_115, plain, ![X22, X23]:(~v1_relat_1(X22)|~v1_funct_1(X22)|(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v2_funct_1(X22)|~v2_funct_1(X23)|v2_funct_1(k5_relat_1(X22,X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_funct_1])])])).
% 0.19/0.54  fof(c_0_116, plain, ![X60]:(v2_struct_0(X60)|~l1_struct_0(X60)|~v1_xboole_0(u1_struct_0(X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.54  cnf(c_0_117, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114])])).
% 0.19/0.54  cnf(c_0_118, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.19/0.54  cnf(c_0_119, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.19/0.54  cnf(c_0_120, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_52]), c_0_46]), c_0_36]), c_0_37]), c_0_66]), c_0_67])])).
% 0.19/0.54  cnf(c_0_121, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_31])]), c_0_121]), ['proof']).
% 0.19/0.54  # SZS output end CNFRefutation
% 0.19/0.54  # Proof object total steps             : 123
% 0.19/0.54  # Proof object clause steps            : 80
% 0.19/0.54  # Proof object formula steps           : 43
% 0.19/0.54  # Proof object conjectures             : 55
% 0.19/0.54  # Proof object clause conjectures      : 52
% 0.19/0.54  # Proof object formula conjectures     : 3
% 0.19/0.54  # Proof object initial clauses used    : 38
% 0.19/0.54  # Proof object initial formulas used   : 21
% 0.19/0.54  # Proof object generating inferences   : 34
% 0.19/0.54  # Proof object simplifying inferences  : 116
% 0.19/0.54  # Training examples: 0 positive, 0 negative
% 0.19/0.54  # Parsed axioms                        : 24
% 0.19/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.54  # Initial clauses                      : 57
% 0.19/0.54  # Removed in clause preprocessing      : 0
% 0.19/0.54  # Initial clauses in saturation        : 57
% 0.19/0.54  # Processed clauses                    : 1653
% 0.19/0.54  # ...of these trivial                  : 4
% 0.19/0.54  # ...subsumed                          : 977
% 0.19/0.54  # ...remaining for further processing  : 672
% 0.19/0.54  # Other redundant clauses eliminated   : 337
% 0.19/0.54  # Clauses deleted for lack of memory   : 0
% 0.19/0.54  # Backward-subsumed                    : 71
% 0.19/0.54  # Backward-rewritten                   : 38
% 0.19/0.54  # Generated clauses                    : 7529
% 0.19/0.54  # ...of the previous two non-trivial   : 6799
% 0.19/0.54  # Contextual simplify-reflections      : 31
% 0.19/0.54  # Paramodulations                      : 7165
% 0.19/0.54  # Factorizations                       : 27
% 0.19/0.54  # Equation resolutions                 : 338
% 0.19/0.54  # Propositional unsat checks           : 0
% 0.19/0.54  #    Propositional check models        : 0
% 0.19/0.54  #    Propositional check unsatisfiable : 0
% 0.19/0.54  #    Propositional clauses             : 0
% 0.19/0.54  #    Propositional clauses after purity: 0
% 0.19/0.54  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 500
% 0.19/0.54  #    Positive orientable unit clauses  : 69
% 0.19/0.54  #    Positive unorientable unit clauses: 0
% 0.19/0.54  #    Negative unit clauses             : 10
% 0.19/0.54  #    Non-unit-clauses                  : 421
% 0.19/0.54  # Current number of unprocessed clauses: 5190
% 0.19/0.54  # ...number of literals in the above   : 26646
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 165
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 55919
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 16798
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 1074
% 0.19/0.54  # Unit Clause-clause subsumption calls : 1654
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 24
% 0.19/0.54  # BW rewrite match successes           : 13
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 201929
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.196 s
% 0.19/0.54  # System time              : 0.013 s
% 0.19/0.54  # Total time               : 0.209 s
% 0.19/0.54  # Maximum resident set size: 1624 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1409+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:15 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 777 expanded)
%              Number of clauses        :   69 ( 262 expanded)
%              Number of leaves         :   19 ( 192 expanded)
%              Depth                    :   11
%              Number of atoms          :  532 (4791 expanded)
%              Number of equality atoms :   40 ( 450 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   88 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_filter_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ! [X5] :
                      ( m2_filter_1(X5,X1,X2)
                     => k1_binop_1(k3_filter_1(X1,X2,X5),k6_eqrel_1(X1,X1,X2,X3),k6_eqrel_1(X1,X1,X2,X4)) = k6_eqrel_1(X1,X1,X2,k4_binop_1(X1,X5,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_filter_1)).

fof(redefinition_k6_eqrel_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_eqrel_1(X1,X2,X3,X4) = k11_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_eqrel_1)).

fof(redefinition_k9_eqrel_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & m1_subset_1(X3,X1) )
     => k9_eqrel_1(X1,X2,X3) = k11_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_eqrel_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(redefinition_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k8_eqrel_1(X1,X2) = k7_eqrel_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(dt_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_eqrel_1(k8_eqrel_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k9_eqrel_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & m1_subset_1(X3,X1) )
     => m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k7_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_subset_1(k7_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

fof(cc1_eqrel_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_eqrel_1(X2,X1)
         => ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_eqrel_1)).

fof(dt_m2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X2) )
     => ! [X3] :
          ( m2_filter_1(X3,X1,X2)
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(t28_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_2(X2)
        & v3_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,k6_eqrel_1(X1,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_eqrel_1)).

fof(redefinition_k4_binop_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & m1_subset_1(X3,X1)
        & m1_subset_1(X4,X1) )
     => k4_binop_1(X1,X2,X3,X4) = k1_binop_1(X2,X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_binop_1)).

fof(d4_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
             => ( m2_filter_1(X3,X1,X2)
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))) )
                   => ( X4 = k3_filter_1(X1,X2,X3)
                    <=> ! [X5,X6,X7,X8] :
                          ( ( r2_hidden(X5,k8_eqrel_1(X1,X2))
                            & r2_hidden(X6,k8_eqrel_1(X1,X2))
                            & r2_hidden(X7,X5)
                            & r2_hidden(X8,X6) )
                         => k1_binop_1(X4,X5,X6) = k6_eqrel_1(X1,X1,X2,k1_binop_1(X3,X7,X8)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_filter_1)).

fof(dt_k3_filter_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_partfun1(X2,X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & v1_funct_1(X3)
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
     => ( v1_funct_1(k3_filter_1(X1,X2,X3))
        & v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
        & m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(cc3_partfun1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v3_relat_2(X1)
        & v8_relat_2(X1) )
     => ( v1_relat_1(X1)
        & v1_relat_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_partfun1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v1_partfun1(X2,X1)
              & v3_relat_2(X2)
              & v8_relat_2(X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => ! [X5] :
                        ( m2_filter_1(X5,X1,X2)
                       => k1_binop_1(k3_filter_1(X1,X2,X5),k6_eqrel_1(X1,X1,X2,X3),k6_eqrel_1(X1,X1,X2,X4)) = k6_eqrel_1(X1,X1,X2,k4_binop_1(X1,X5,X3,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_filter_1])).

fof(c_0_20,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | k6_eqrel_1(X46,X47,X48,X49) = k11_relat_1(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_eqrel_1])])).

fof(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    & v1_partfun1(esk7_0,esk6_0)
    & v3_relat_2(esk7_0)
    & v8_relat_2(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0)))
    & m1_subset_1(esk8_0,esk6_0)
    & m1_subset_1(esk9_0,esk6_0)
    & m2_filter_1(esk10_0,esk6_0,esk7_0)
    & k1_binop_1(k3_filter_1(esk6_0,esk7_0,esk10_0),k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0),k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0)) != k6_eqrel_1(esk6_0,esk6_0,esk7_0,k4_binop_1(esk6_0,esk10_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_22,plain,(
    ! [X52,X53,X54] :
      ( v1_xboole_0(X52)
      | ~ v3_relat_2(X53)
      | ~ v8_relat_2(X53)
      | ~ v1_partfun1(X53,X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X52,X52)))
      | ~ m1_subset_1(X54,X52)
      | k9_eqrel_1(X52,X53,X54) = k11_relat_1(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k9_eqrel_1])])])).

cnf(c_0_23,plain,
    ( k6_eqrel_1(X2,X3,X1,X4) = k11_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X61,X62] :
      ( ~ m1_subset_1(X61,X62)
      | v1_xboole_0(X62)
      | r2_hidden(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_26,plain,(
    ! [X40] : m1_subset_1(esk5_1(X40),X40) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_27,plain,(
    ! [X50,X51] :
      ( ~ v3_relat_2(X51)
      | ~ v8_relat_2(X51)
      | ~ v1_partfun1(X51,X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X50)))
      | k8_eqrel_1(X50,X51) = k7_eqrel_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_eqrel_1])])).

fof(c_0_28,plain,(
    ! [X32,X33] :
      ( ~ v3_relat_2(X33)
      | ~ v8_relat_2(X33)
      | ~ v1_partfun1(X33,X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X32,X32)))
      | m1_eqrel_1(k8_eqrel_1(X32,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_eqrel_1])])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,plain,(
    ! [X34,X35,X36] :
      ( v1_xboole_0(X34)
      | ~ v3_relat_2(X35)
      | ~ v8_relat_2(X35)
      | ~ v1_partfun1(X35,X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X34)))
      | ~ m1_subset_1(X36,X34)
      | m2_subset_1(k9_eqrel_1(X34,X35,X36),k1_zfmisc_1(X34),k8_eqrel_1(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | k9_eqrel_1(X1,X2,X3) = k11_relat_1(X2,X3)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_partfun1(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( k11_relat_1(esk7_0,X1) = k6_eqrel_1(esk6_0,esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v8_relat_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v3_relat_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_37,plain,(
    ! [X63,X64,X65] :
      ( ~ r2_hidden(X63,X64)
      | ~ m1_subset_1(X64,k1_zfmisc_1(X65))
      | ~ v1_xboole_0(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_40,plain,(
    ! [X30,X31] :
      ( ~ v3_relat_2(X31)
      | ~ v8_relat_2(X31)
      | ~ v1_partfun1(X31,X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X30)))
      | m1_subset_1(k7_eqrel_1(X30,X31),k1_zfmisc_1(k1_zfmisc_1(X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_eqrel_1])])).

cnf(c_0_41,plain,
    ( k8_eqrel_1(X2,X1) = k7_eqrel_1(X2,X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_42,plain,(
    ! [X9,X10] :
      ( v1_xboole_0(X9)
      | ~ m1_eqrel_1(X10,X9)
      | ~ v1_xboole_0(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_eqrel_1])])])])).

cnf(c_0_43,plain,
    ( m1_eqrel_1(k8_eqrel_1(X2,X1),X2)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_44,plain,(
    ! [X37,X38,X39] :
      ( ( v1_funct_1(X39)
        | ~ m2_filter_1(X39,X37,X38)
        | v1_xboole_0(X37)
        | ~ v1_relat_1(X38) )
      & ( v1_funct_2(X39,k2_zfmisc_1(X37,X37),X37)
        | ~ m2_filter_1(X39,X37,X38)
        | v1_xboole_0(X37)
        | ~ v1_relat_1(X38) )
      & ( m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X37,X37),X37)))
        | ~ m2_filter_1(X39,X37,X38)
        | v1_xboole_0(X37)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_46,plain,(
    ! [X58,X59,X60] :
      ( ~ v1_relat_2(X59)
      | ~ v3_relat_2(X59)
      | ~ v1_partfun1(X59,X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X58,X58)))
      | ~ r2_hidden(X60,X58)
      | r2_hidden(X60,k6_eqrel_1(X58,X58,X59,X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_eqrel_1])])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( k9_eqrel_1(esk6_0,esk7_0,X1) = k6_eqrel_1(esk6_0,esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_24])]),c_0_36])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,plain,
    ( m1_subset_1(k7_eqrel_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( k7_eqrel_1(esk6_0,esk7_0) = k8_eqrel_1(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_34]),c_0_35]),c_0_24])])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | ~ m1_eqrel_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( m1_eqrel_1(k8_eqrel_1(esk6_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_32]),c_0_34]),c_0_35]),c_0_24])])).

fof(c_0_56,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,k2_zfmisc_1(X42,X42),X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,X42),X42)))
      | ~ m1_subset_1(X44,X42)
      | ~ m1_subset_1(X45,X42)
      | k4_binop_1(X42,X43,X44,X45) = k1_binop_1(X43,X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_binop_1])])).

cnf(c_0_57,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( m2_filter_1(esk10_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_60,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_62,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( X18 != k3_filter_1(X15,X16,X17)
        | ~ r2_hidden(X19,k8_eqrel_1(X15,X16))
        | ~ r2_hidden(X20,k8_eqrel_1(X15,X16))
        | ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X22,X20)
        | k1_binop_1(X18,X19,X20) = k6_eqrel_1(X15,X15,X16,k1_binop_1(X17,X21,X22))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))))
        | ~ m2_filter_1(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_partfun1(X16,X15)
        | ~ v3_relat_2(X16)
        | ~ v8_relat_2(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15)))
        | v1_xboole_0(X15) )
      & ( r2_hidden(esk1_4(X15,X16,X17,X18),k8_eqrel_1(X15,X16))
        | X18 = k3_filter_1(X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))))
        | ~ m2_filter_1(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_partfun1(X16,X15)
        | ~ v3_relat_2(X16)
        | ~ v8_relat_2(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15)))
        | v1_xboole_0(X15) )
      & ( r2_hidden(esk2_4(X15,X16,X17,X18),k8_eqrel_1(X15,X16))
        | X18 = k3_filter_1(X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))))
        | ~ m2_filter_1(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_partfun1(X16,X15)
        | ~ v3_relat_2(X16)
        | ~ v8_relat_2(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15)))
        | v1_xboole_0(X15) )
      & ( r2_hidden(esk3_4(X15,X16,X17,X18),esk1_4(X15,X16,X17,X18))
        | X18 = k3_filter_1(X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))))
        | ~ m2_filter_1(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_partfun1(X16,X15)
        | ~ v3_relat_2(X16)
        | ~ v8_relat_2(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15)))
        | v1_xboole_0(X15) )
      & ( r2_hidden(esk4_4(X15,X16,X17,X18),esk2_4(X15,X16,X17,X18))
        | X18 = k3_filter_1(X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))))
        | ~ m2_filter_1(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_partfun1(X16,X15)
        | ~ v3_relat_2(X16)
        | ~ v8_relat_2(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15)))
        | v1_xboole_0(X15) )
      & ( k1_binop_1(X18,esk1_4(X15,X16,X17,X18),esk2_4(X15,X16,X17,X18)) != k6_eqrel_1(X15,X15,X16,k1_binop_1(X17,esk3_4(X15,X16,X17,X18),esk4_4(X15,X16,X17,X18)))
        | X18 = k3_filter_1(X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X15,X16),k8_eqrel_1(X15,X16)),k8_eqrel_1(X15,X16))))
        | ~ m2_filter_1(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_partfun1(X16,X15)
        | ~ v3_relat_2(X16)
        | ~ v8_relat_2(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15)))
        | v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_filter_1])])])])])])).

fof(c_0_63,plain,(
    ! [X27,X28,X29] :
      ( ( v1_funct_1(k3_filter_1(X27,X28,X29))
        | v1_xboole_0(X27)
        | ~ v1_partfun1(X28,X27)
        | ~ v3_relat_2(X28)
        | ~ v8_relat_2(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X27)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,k2_zfmisc_1(X27,X27),X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X27,X27),X27))) )
      & ( v1_funct_2(k3_filter_1(X27,X28,X29),k2_zfmisc_1(k8_eqrel_1(X27,X28),k8_eqrel_1(X27,X28)),k8_eqrel_1(X27,X28))
        | v1_xboole_0(X27)
        | ~ v1_partfun1(X28,X27)
        | ~ v3_relat_2(X28)
        | ~ v8_relat_2(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X27)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,k2_zfmisc_1(X27,X27),X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X27,X27),X27))) )
      & ( m1_subset_1(k3_filter_1(X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X27,X28),k8_eqrel_1(X27,X28)),k8_eqrel_1(X27,X28))))
        | v1_xboole_0(X27)
        | ~ v1_partfun1(X28,X27)
        | ~ v3_relat_2(X28)
        | ~ v8_relat_2(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X27)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,k2_zfmisc_1(X27,X27),X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X27,X27),X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,k6_eqrel_1(X2,X2,X1,X3))
    | ~ v1_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk9_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_47]),c_0_36])).

fof(c_0_66,plain,(
    ! [X55,X56,X57] :
      ( ( ~ m2_subset_1(X57,X55,X56)
        | m1_subset_1(X57,X56)
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(X55)) )
      & ( ~ m1_subset_1(X57,X56)
        | m2_subset_1(X57,X55,X56)
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(X55)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

cnf(c_0_67,negated_conjecture,
    ( m2_subset_1(k9_eqrel_1(esk6_0,esk7_0,X1),k1_zfmisc_1(esk6_0),k8_eqrel_1(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32]),c_0_34]),c_0_35]),c_0_24])]),c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( k9_eqrel_1(esk6_0,esk7_0,esk9_0) = k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_47])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k8_eqrel_1(esk6_0,esk7_0),k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_53]),c_0_34]),c_0_35]),c_0_24])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(k8_eqrel_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_73,plain,
    ( k4_binop_1(X2,X1,X3,X4) = k1_binop_1(X1,X3,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X3,X2)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk10_0,k2_zfmisc_1(esk6_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_59])]),c_0_36])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_59])]),c_0_36])).

cnf(c_0_77,plain,
    ( k1_binop_1(X1,X5,X6) = k6_eqrel_1(X2,X2,X3,k1_binop_1(X4,X7,X8))
    | v1_xboole_0(X2)
    | X1 != k3_filter_1(X2,X3,X4)
    | ~ r2_hidden(X5,k8_eqrel_1(X2,X3))
    | ~ r2_hidden(X6,k8_eqrel_1(X2,X3))
    | ~ r2_hidden(X7,X5)
    | ~ r2_hidden(X8,X6)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_zfmisc_1(k8_eqrel_1(X2,X3),k8_eqrel_1(X2,X3)),k8_eqrel_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X2,X3),k8_eqrel_1(X2,X3)),k8_eqrel_1(X2,X3))))
    | ~ m2_filter_1(X4,X2,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ v1_partfun1(X3,X2)
    | ~ v3_relat_2(X3)
    | ~ v8_relat_2(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk9_0,k6_eqrel_1(esk6_0,esk6_0,X1,esk9_0))
    | ~ v1_partfun1(X1,esk6_0)
    | ~ v1_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_82,plain,(
    ! [X14] :
      ( ( v1_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v3_relat_2(X14)
        | ~ v8_relat_2(X14) )
      & ( v1_relat_2(X14)
        | ~ v1_relat_1(X14)
        | ~ v3_relat_2(X14)
        | ~ v8_relat_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_partfun1])])])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_84,negated_conjecture,
    ( m2_subset_1(k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0),k1_zfmisc_1(esk6_0),k8_eqrel_1(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_47]),c_0_68])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_72]),c_0_36])).

cnf(c_0_87,negated_conjecture,
    ( k9_eqrel_1(esk6_0,esk7_0,esk8_0) = k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_72])).

cnf(c_0_88,negated_conjecture,
    ( k4_binop_1(esk6_0,esk10_0,X1,X2) = k1_binop_1(esk10_0,X1,X2)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])])).

cnf(c_0_89,plain,
    ( k1_binop_1(k3_filter_1(X1,X2,X3),X4,X5) = k6_eqrel_1(X1,X1,X2,k1_binop_1(X3,X6,X7))
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X4,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X7,X5)
    | ~ r2_hidden(X6,X4)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_partfun1(X2,X1)
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_77]),c_0_78]),c_0_79]),c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk9_0,k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0))
    | ~ v1_relat_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_32]),c_0_35]),c_0_24])])).

cnf(c_0_91,plain,
    ( v1_relat_2(X1)
    | ~ v1_relat_1(X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0),k8_eqrel_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_70])]),c_0_71]),c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk8_0,k6_eqrel_1(esk6_0,esk6_0,X1,esk8_0))
    | ~ v1_partfun1(X1,esk6_0)
    | ~ v1_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( m2_subset_1(k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0),k1_zfmisc_1(esk6_0),k8_eqrel_1(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_72]),c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( k4_binop_1(esk6_0,esk10_0,X1,esk9_0) = k1_binop_1(esk10_0,X1,esk9_0)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_47])).

cnf(c_0_96,negated_conjecture,
    ( k1_binop_1(k3_filter_1(esk6_0,esk7_0,esk10_0),X1,X2) = k6_eqrel_1(esk6_0,esk6_0,esk7_0,k1_binop_1(esk10_0,X3,X4))
    | ~ r2_hidden(X2,k8_eqrel_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,k8_eqrel_1(esk6_0,esk7_0))
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_58]),c_0_74]),c_0_75]),c_0_32]),c_0_34]),c_0_35]),c_0_76]),c_0_24])]),c_0_36])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk9_0,k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_34]),c_0_35]),c_0_59])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0),k8_eqrel_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_92]),c_0_71])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk8_0,k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0))
    | ~ v1_relat_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_32]),c_0_35]),c_0_24])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0),k8_eqrel_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_94]),c_0_70])]),c_0_71]),c_0_85])).

cnf(c_0_101,negated_conjecture,
    ( k1_binop_1(k3_filter_1(esk6_0,esk7_0,esk10_0),k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0),k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0)) != k6_eqrel_1(esk6_0,esk6_0,esk7_0,k4_binop_1(esk6_0,esk10_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_102,negated_conjecture,
    ( k4_binop_1(esk6_0,esk10_0,esk8_0,esk9_0) = k1_binop_1(esk10_0,esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_72])).

cnf(c_0_103,negated_conjecture,
    ( k1_binop_1(k3_filter_1(esk6_0,esk7_0,esk10_0),X1,k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0)) = k6_eqrel_1(esk6_0,esk6_0,esk7_0,k1_binop_1(esk10_0,X2,esk9_0))
    | ~ r2_hidden(X1,k8_eqrel_1(esk6_0,esk7_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk8_0,k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_91]),c_0_34]),c_0_35]),c_0_59])])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0),k8_eqrel_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_100]),c_0_71])).

cnf(c_0_106,negated_conjecture,
    ( k1_binop_1(k3_filter_1(esk6_0,esk7_0,esk10_0),k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk8_0),k6_eqrel_1(esk6_0,esk6_0,esk7_0,esk9_0)) != k6_eqrel_1(esk6_0,esk6_0,esk7_0,k1_binop_1(esk10_0,esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])]),c_0_106]),
    [proof]).

%------------------------------------------------------------------------------

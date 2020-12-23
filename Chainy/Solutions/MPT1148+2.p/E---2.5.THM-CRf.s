%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1148+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:02 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   35 (  88 expanded)
%              Number of clauses        :   20 (  35 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  118 ( 312 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_orders_2,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_wellord1(u1_orders_2(X1),X2)
           => ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_wellord1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2)
            & r1_wellord1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT010+2.ax',d5_wellord1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(t92_orders_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r7_relat_2(X2,X1)
      <=> ( r1_relat_2(X2,X1)
          & r6_relat_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_wellord1(u1_orders_2(X1),X2)
             => ( v6_orders_2(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_orders_2])).

fof(c_0_8,plain,(
    ! [X261] :
      ( ~ l1_orders_2(X261)
      | m1_subset_1(u1_orders_2(X261),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X261),u1_struct_0(X261)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & r2_wellord1(u1_orders_2(esk1_0),esk2_0)
    & ( ~ v6_orders_2(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X240,X241] :
      ( ( r1_relat_2(X240,X241)
        | ~ r2_wellord1(X240,X241)
        | ~ v1_relat_1(X240) )
      & ( r8_relat_2(X240,X241)
        | ~ r2_wellord1(X240,X241)
        | ~ v1_relat_1(X240) )
      & ( r4_relat_2(X240,X241)
        | ~ r2_wellord1(X240,X241)
        | ~ v1_relat_1(X240) )
      & ( r6_relat_2(X240,X241)
        | ~ r2_wellord1(X240,X241)
        | ~ v1_relat_1(X240) )
      & ( r1_wellord1(X240,X241)
        | ~ r2_wellord1(X240,X241)
        | ~ v1_relat_1(X240) )
      & ( ~ r1_relat_2(X240,X241)
        | ~ r8_relat_2(X240,X241)
        | ~ r4_relat_2(X240,X241)
        | ~ r6_relat_2(X240,X241)
        | ~ r1_wellord1(X240,X241)
        | r2_wellord1(X240,X241)
        | ~ v1_relat_1(X240) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_wellord1])])])])).

fof(c_0_11,plain,(
    ! [X85,X86] :
      ( ~ v1_relat_1(X85)
      | ~ m1_subset_1(X86,k1_zfmisc_1(X85))
      | v1_relat_1(X86) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X1898,X1899] : v1_relat_1(k2_zfmisc_1(X1898,X1899)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_15,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_wellord1(u1_orders_2(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X218,X219] :
      ( ( ~ v6_orders_2(X219,X218)
        | r7_relat_2(u1_orders_2(X218),X219)
        | ~ m1_subset_1(X219,k1_zfmisc_1(u1_struct_0(X218)))
        | ~ l1_orders_2(X218) )
      & ( ~ r7_relat_2(u1_orders_2(X218),X219)
        | v6_orders_2(X219,X218)
        | ~ m1_subset_1(X219,k1_zfmisc_1(u1_struct_0(X218)))
        | ~ l1_orders_2(X218) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ v6_orders_2(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_24,plain,(
    ! [X2850,X2851] :
      ( ( r1_relat_2(X2851,X2850)
        | ~ r7_relat_2(X2851,X2850)
        | ~ v1_relat_1(X2851) )
      & ( r6_relat_2(X2851,X2850)
        | ~ r7_relat_2(X2851,X2850)
        | ~ v1_relat_1(X2851) )
      & ( ~ r1_relat_2(X2851,X2850)
        | ~ r6_relat_2(X2851,X2850)
        | r7_relat_2(X2851,X2850)
        | ~ v1_relat_1(X2851) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_orders_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk1_0),esk2_0)
    | ~ v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_27,negated_conjecture,
    ( r6_relat_2(u1_orders_2(esk1_0),esk2_0)
    | ~ v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_28,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( ~ v6_orders_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_30,plain,
    ( r7_relat_2(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( r6_relat_2(u1_orders_2(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r7_relat_2(u1_orders_2(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_13])]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_26])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------

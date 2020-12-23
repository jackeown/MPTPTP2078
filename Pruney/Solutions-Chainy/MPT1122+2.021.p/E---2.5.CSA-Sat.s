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
% DateTime   : Thu Dec  3 11:09:16 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 166 expanded)
%              Number of clauses        :   27 (  66 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 788 expanded)
%              Number of equality atoms :   29 ( 171 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(t53_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
             => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

fof(c_0_6,plain,(
    ! [X7,X8] :
      ( ( ~ v4_pre_topc(X8,X7)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X7),k2_struct_0(X7),X8),X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X7),k2_struct_0(X7),X8),X7)
        | v4_pre_topc(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

fof(c_0_7,plain,(
    ! [X10,X11] :
      ( ~ l1_struct_0(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | k7_subset_1(u1_struct_0(X10),k2_struct_0(X10),k7_subset_1(u1_struct_0(X10),k2_struct_0(X10),X11)) = X11 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

fof(c_0_8,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_9,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_12,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | m1_subset_1(k7_subset_1(X4,X5,X6),k1_zfmisc_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ( ~ v4_pre_topc(X13,X12)
        | k2_pre_topc(X12,X13) = X13
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( ~ v2_pre_topc(X12)
        | k2_pre_topc(X12,X13) != X13
        | v4_pre_topc(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_14,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_15,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),
    [final]).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_17,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v3_pre_topc(X2,X1)
               => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
              & ( ( v2_pre_topc(X1)
                  & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
               => v3_pre_topc(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_pre_topc])).

cnf(c_0_19,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_20,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11]),
    [final]).

cnf(c_0_21,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_22,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),X2,X3),X1)
    | k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3)) != k7_subset_1(u1_struct_0(X1),X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16]),
    [final]).

fof(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( v2_pre_topc(esk1_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( v2_pre_topc(esk1_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) )
    & ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) )
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])).

cnf(c_0_24,plain,
    ( k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3)) = k7_subset_1(u1_struct_0(X1),X2,X3)
    | ~ v4_pre_topc(k7_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16]),
    [final]).

cnf(c_0_25,plain,
    ( v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16]),
    [final]).

cnf(c_0_26,plain,
    ( v3_pre_topc(X1,X2)
    | k2_pre_topc(X2,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)) != k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_31,plain,
    ( k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_34,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_10]),c_0_16]),c_0_11]),
    [final]).

cnf(c_0_35,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_10]),c_0_16]),c_0_11]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_pre_topc(esk1_0,esk2_0) != esk2_0
    | ~ v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_29]),c_0_28])]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_29]),c_0_28])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    | k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_28]),c_0_29])]),c_0_33]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:33:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S013N
% 0.13/0.38  # and selection function PSelectGroundNegLit.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 0.13/0.38  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 0.13/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.13/0.38  fof(t53_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_pre_topc)).
% 0.13/0.38  fof(c_0_6, plain, ![X7, X8]:((~v4_pre_topc(X8,X7)|v3_pre_topc(k7_subset_1(u1_struct_0(X7),k2_struct_0(X7),X8),X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X7),k2_struct_0(X7),X8),X7)|v4_pre_topc(X8,X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_pre_topc(X7))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X10, X11]:(~l1_struct_0(X10)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|k7_subset_1(u1_struct_0(X10),k2_struct_0(X10),k7_subset_1(u1_struct_0(X10),k2_struct_0(X10),X11))=X11)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_9, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_10, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_11, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  fof(c_0_12, plain, ![X4, X5, X6]:(~m1_subset_1(X5,k1_zfmisc_1(X4))|m1_subset_1(k7_subset_1(X4,X5,X6),k1_zfmisc_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 0.13/0.38  fof(c_0_13, plain, ![X12, X13]:((~v4_pre_topc(X13,X12)|k2_pre_topc(X12,X13)=X13|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~v2_pre_topc(X12)|k2_pre_topc(X12,X13)!=X13|v4_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.38  cnf(c_0_15, plain, (v3_pre_topc(X1,X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_16, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_17, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1)))))), inference(assume_negation,[status(cth)],[t53_pre_topc])).
% 0.13/0.38  cnf(c_0_19, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_20, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_21, plain, (v3_pre_topc(X1,X2)|~v4_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.13/0.38  cnf(c_0_22, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),X2,X3),X1)|k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3))!=k7_subset_1(u1_struct_0(X1),X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_17, c_0_16]), ['final']).
% 0.13/0.38  fof(c_0_23, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((((v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)))&(~v3_pre_topc(esk2_0,esk1_0)|v3_pre_topc(esk2_0,esk1_0)))&(((v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))&(k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))&(~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])).
% 0.13/0.38  cnf(c_0_24, plain, (k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),X2,X3))=k7_subset_1(u1_struct_0(X1),X2,X3)|~v4_pre_topc(k7_subset_1(u1_struct_0(X1),X2,X3),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_19, c_0_16]), ['final']).
% 0.13/0.38  cnf(c_0_25, plain, (v4_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_16]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (v3_pre_topc(X1,X2)|k2_pre_topc(X2,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))!=k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk1_0)|v3_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_31, plain, (k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.13/0.38  cnf(c_0_34, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|k2_pre_topc(X1,X2)!=X2|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_10]), c_0_16]), c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_35, plain, (k2_pre_topc(X1,X2)=X2|~v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_10]), c_0_16]), c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_pre_topc(esk1_0,esk2_0)!=esk2_0|~v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_29]), c_0_28])]), ['final']).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_29]), c_0_28])]), ['final']).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk1_0)|k2_pre_topc(esk1_0,k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_28]), c_0_29])]), c_0_33]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 40
% 0.13/0.38  # Proof object clause steps            : 27
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 13
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 14
% 0.13/0.38  # Proof object simplifying inferences  : 18
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 15
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 13
% 0.13/0.38  # Processed clauses                    : 52
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 12
% 0.13/0.38  # ...remaining for further processing  : 40
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 33
% 0.13/0.38  # ...of the previous two non-trivial   : 26
% 0.13/0.38  # Contextual simplify-reflections      : 8
% 0.13/0.38  # Paramodulations                      : 33
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
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
% 0.13/0.38  # Current number of processed clauses  : 27
% 0.13/0.38  #    Positive orientable unit clauses  : 2
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 24
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 13
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 269
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 47
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 19
% 0.13/0.38  # Unit Clause-clause subsumption calls : 1
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2409
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

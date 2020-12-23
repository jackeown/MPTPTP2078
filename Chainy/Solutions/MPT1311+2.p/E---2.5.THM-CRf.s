%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1311+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:04 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :   23 (  61 expanded)
%              Number of clauses        :   14 (  20 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  101 ( 279 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t4_subset)).

fof(t29_tops_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_2)).

fof(t44_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',t44_pre_topc)).

fof(c_0_4,plain,(
    ! [X7087,X7088,X7089] :
      ( ( ~ v2_tops_2(X7088,X7087)
        | ~ m1_subset_1(X7089,k1_zfmisc_1(u1_struct_0(X7087)))
        | ~ r2_hidden(X7089,X7088)
        | v4_pre_topc(X7089,X7087)
        | ~ m1_subset_1(X7088,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7087))))
        | ~ l1_pre_topc(X7087) )
      & ( m1_subset_1(esk722_2(X7087,X7088),k1_zfmisc_1(u1_struct_0(X7087)))
        | v2_tops_2(X7088,X7087)
        | ~ m1_subset_1(X7088,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7087))))
        | ~ l1_pre_topc(X7087) )
      & ( r2_hidden(esk722_2(X7087,X7088),X7088)
        | v2_tops_2(X7088,X7087)
        | ~ m1_subset_1(X7088,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7087))))
        | ~ l1_pre_topc(X7087) )
      & ( ~ v4_pre_topc(esk722_2(X7087,X7088),X7087)
        | v2_tops_2(X7088,X7087)
        | ~ m1_subset_1(X7088,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7087))))
        | ~ l1_pre_topc(X7087) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

fof(c_0_5,plain,(
    ! [X2040,X2041,X2042] :
      ( ~ r2_hidden(X2040,X2041)
      | ~ m1_subset_1(X2041,k1_zfmisc_1(X2042))
      | m1_subset_1(X2040,X2042) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v2_tops_2(X2,X1)
             => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tops_2])).

cnf(c_0_7,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,
    ( v2_pre_topc(esk736_0)
    & l1_pre_topc(esk736_0)
    & m1_subset_1(esk737_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk736_0))))
    & v2_tops_2(esk737_0,esk736_0)
    & ~ v4_pre_topc(k6_setfam_1(u1_struct_0(esk736_0),esk737_0),esk736_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X6017,X6018] :
      ( ( m1_subset_1(esk624_2(X6017,X6018),k1_zfmisc_1(u1_struct_0(X6017)))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X6017),X6018),X6017)
        | ~ m1_subset_1(X6018,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6017))))
        | ~ v2_pre_topc(X6017)
        | ~ l1_pre_topc(X6017) )
      & ( r2_hidden(esk624_2(X6017,X6018),X6018)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X6017),X6018),X6017)
        | ~ m1_subset_1(X6018,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6017))))
        | ~ v2_pre_topc(X6017)
        | ~ l1_pre_topc(X6017) )
      & ( ~ v4_pre_topc(esk624_2(X6017,X6018),X6017)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X6017),X6018),X6017)
        | ~ m1_subset_1(X6018,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6017))))
        | ~ v2_pre_topc(X6017)
        | ~ l1_pre_topc(X6017) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).

cnf(c_0_11,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v2_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(csr,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk737_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk736_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_tops_2(esk737_0,esk736_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk736_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk624_2(X1,X2),X2)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk736_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(esk736_0),esk737_0),esk736_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(esk624_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v4_pre_topc(X1,esk736_0)
    | ~ r2_hidden(X1,esk737_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk624_2(esk736_0,esk737_0),esk737_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_16]),c_0_14])]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v4_pre_topc(esk624_2(esk736_0,esk737_0),esk736_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_12]),c_0_16]),c_0_14])]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------

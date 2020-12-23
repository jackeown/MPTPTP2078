%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1790+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 13.07s
% Output     : CNFRefutation 13.07s
% Verified   : 
% Statistics : Number of formulae       :   29 (  83 expanded)
%              Number of clauses        :   18 (  27 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :  114 ( 438 expanded)
%              Number of equality atoms :   10 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t105_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
             => ( X3 = X2
               => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',d5_pre_topc)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t102_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
               => ( X3 = X2
                 => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t105_tmap_1])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1266_0)
    & v2_pre_topc(esk1266_0)
    & l1_pre_topc(esk1266_0)
    & m1_subset_1(esk1267_0,k1_zfmisc_1(u1_struct_0(esk1266_0)))
    & m1_subset_1(esk1268_0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk1266_0,esk1267_0))))
    & esk1268_0 = esk1267_0
    & ~ v3_pre_topc(esk1268_0,k6_tmap_1(esk1266_0,esk1267_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X10685,X10686] :
      ( ( v1_pre_topc(k6_tmap_1(X10685,X10686))
        | v2_struct_0(X10685)
        | ~ v2_pre_topc(X10685)
        | ~ l1_pre_topc(X10685)
        | ~ m1_subset_1(X10686,k1_zfmisc_1(u1_struct_0(X10685))) )
      & ( v2_pre_topc(k6_tmap_1(X10685,X10686))
        | v2_struct_0(X10685)
        | ~ v2_pre_topc(X10685)
        | ~ l1_pre_topc(X10685)
        | ~ m1_subset_1(X10686,k1_zfmisc_1(u1_struct_0(X10685))) )
      & ( l1_pre_topc(k6_tmap_1(X10685,X10686))
        | v2_struct_0(X10685)
        | ~ v2_pre_topc(X10685)
        | ~ l1_pre_topc(X10685)
        | ~ m1_subset_1(X10686,k1_zfmisc_1(u1_struct_0(X10685))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_8,plain,(
    ! [X5897,X5898] :
      ( ( ~ v3_pre_topc(X5898,X5897)
        | r2_hidden(X5898,u1_pre_topc(X5897))
        | ~ m1_subset_1(X5898,k1_zfmisc_1(u1_struct_0(X5897)))
        | ~ l1_pre_topc(X5897) )
      & ( ~ r2_hidden(X5898,u1_pre_topc(X5897))
        | v3_pre_topc(X5898,X5897)
        | ~ m1_subset_1(X5898,k1_zfmisc_1(u1_struct_0(X5897)))
        | ~ l1_pre_topc(X5897) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk1268_0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk1266_0,esk1267_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk1268_0 = esk1267_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk1267_0,k1_zfmisc_1(u1_struct_0(esk1266_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk1266_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1266_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1266_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( ~ v3_pre_topc(esk1268_0,k6_tmap_1(esk1266_0,esk1267_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_17,plain,(
    ! [X10742,X10743] :
      ( ( u1_struct_0(k6_tmap_1(X10742,X10743)) = u1_struct_0(X10742)
        | ~ m1_subset_1(X10743,k1_zfmisc_1(u1_struct_0(X10742)))
        | v2_struct_0(X10742)
        | ~ v2_pre_topc(X10742)
        | ~ l1_pre_topc(X10742) )
      & ( u1_pre_topc(k6_tmap_1(X10742,X10743)) = k5_tmap_1(X10742,X10743)
        | ~ m1_subset_1(X10743,k1_zfmisc_1(u1_struct_0(X10742)))
        | v2_struct_0(X10742)
        | ~ v2_pre_topc(X10742)
        | ~ l1_pre_topc(X10742) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_18,plain,(
    ! [X10738,X10739] :
      ( v2_struct_0(X10738)
      | ~ v2_pre_topc(X10738)
      | ~ l1_pre_topc(X10738)
      | ~ m1_subset_1(X10739,k1_zfmisc_1(u1_struct_0(X10738)))
      | r2_hidden(X10739,k5_tmap_1(X10738,X10739)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).

cnf(c_0_19,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk1267_0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(esk1266_0,esk1267_0)))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk1266_0,esk1267_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v3_pre_topc(esk1267_0,k6_tmap_1(esk1266_0,esk1267_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_23,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk1267_0,u1_pre_topc(k6_tmap_1(esk1266_0,esk1267_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk1266_0,esk1267_0)) = k5_tmap_1(esk1266_0,esk1267_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1267_0,k5_tmap_1(esk1266_0,esk1267_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------

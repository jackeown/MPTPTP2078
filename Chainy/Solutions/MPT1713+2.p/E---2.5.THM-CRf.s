%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1713+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 168 expanded)
%              Number of clauses        :   26 (  65 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  192 ( 870 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( m1_pre_topc(X2,X3)
               => ( ~ r1_tsep_1(X2,X3)
                  & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',dt_l1_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d9_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t69_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( m1_pre_topc(X2,X3)
                 => ( ~ r1_tsep_1(X2,X3)
                    & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_tmap_1])).

fof(c_0_10,plain,(
    ! [X5918,X5919] :
      ( ~ l1_pre_topc(X5918)
      | ~ m1_pre_topc(X5919,X5918)
      | l1_pre_topc(X5919) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1267_0)
    & v2_pre_topc(esk1267_0)
    & l1_pre_topc(esk1267_0)
    & ~ v2_struct_0(esk1268_0)
    & m1_pre_topc(esk1268_0,esk1267_0)
    & ~ v2_struct_0(esk1269_0)
    & m1_pre_topc(esk1269_0,esk1267_0)
    & m1_pre_topc(esk1268_0,esk1269_0)
    & ( r1_tsep_1(esk1268_0,esk1269_0)
      | r1_tsep_1(esk1269_0,esk1268_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X5917] :
      ( ~ l1_pre_topc(X5917)
      | l1_struct_0(X5917) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk1268_0,esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk1269_0,esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X5901,X5902,X5903,X5905,X5907] :
      ( ( r1_tarski(k2_struct_0(X5902),k2_struct_0(X5901))
        | ~ m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( m1_subset_1(esk602_3(X5901,X5902,X5903),k1_zfmisc_1(u1_struct_0(X5901)))
        | ~ r2_hidden(X5903,u1_pre_topc(X5902))
        | ~ m1_subset_1(X5903,k1_zfmisc_1(u1_struct_0(X5902)))
        | ~ m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( r2_hidden(esk602_3(X5901,X5902,X5903),u1_pre_topc(X5901))
        | ~ r2_hidden(X5903,u1_pre_topc(X5902))
        | ~ m1_subset_1(X5903,k1_zfmisc_1(u1_struct_0(X5902)))
        | ~ m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( X5903 = k9_subset_1(u1_struct_0(X5902),esk602_3(X5901,X5902,X5903),k2_struct_0(X5902))
        | ~ r2_hidden(X5903,u1_pre_topc(X5902))
        | ~ m1_subset_1(X5903,k1_zfmisc_1(u1_struct_0(X5902)))
        | ~ m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( ~ m1_subset_1(X5905,k1_zfmisc_1(u1_struct_0(X5901)))
        | ~ r2_hidden(X5905,u1_pre_topc(X5901))
        | X5903 != k9_subset_1(u1_struct_0(X5902),X5905,k2_struct_0(X5902))
        | r2_hidden(X5903,u1_pre_topc(X5902))
        | ~ m1_subset_1(X5903,k1_zfmisc_1(u1_struct_0(X5902)))
        | ~ m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( m1_subset_1(esk603_2(X5901,X5902),k1_zfmisc_1(u1_struct_0(X5902)))
        | ~ r1_tarski(k2_struct_0(X5902),k2_struct_0(X5901))
        | m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( ~ r2_hidden(esk603_2(X5901,X5902),u1_pre_topc(X5902))
        | ~ m1_subset_1(X5907,k1_zfmisc_1(u1_struct_0(X5901)))
        | ~ r2_hidden(X5907,u1_pre_topc(X5901))
        | esk603_2(X5901,X5902) != k9_subset_1(u1_struct_0(X5902),X5907,k2_struct_0(X5902))
        | ~ r1_tarski(k2_struct_0(X5902),k2_struct_0(X5901))
        | m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( m1_subset_1(esk604_2(X5901,X5902),k1_zfmisc_1(u1_struct_0(X5901)))
        | r2_hidden(esk603_2(X5901,X5902),u1_pre_topc(X5902))
        | ~ r1_tarski(k2_struct_0(X5902),k2_struct_0(X5901))
        | m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( r2_hidden(esk604_2(X5901,X5902),u1_pre_topc(X5901))
        | r2_hidden(esk603_2(X5901,X5902),u1_pre_topc(X5902))
        | ~ r1_tarski(k2_struct_0(X5902),k2_struct_0(X5901))
        | m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) )
      & ( esk603_2(X5901,X5902) = k9_subset_1(u1_struct_0(X5902),esk604_2(X5901,X5902),k2_struct_0(X5902))
        | r2_hidden(esk603_2(X5901,X5902),u1_pre_topc(X5902))
        | ~ r1_tarski(k2_struct_0(X5902),k2_struct_0(X5901))
        | m1_pre_topc(X5902,X5901)
        | ~ l1_pre_topc(X5902)
        | ~ l1_pre_topc(X5901) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_18,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1268_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1269_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_16]),c_0_15])])).

fof(c_0_22,plain,(
    ! [X10653,X10654] :
      ( ~ l1_struct_0(X10653)
      | ~ l1_struct_0(X10654)
      | ~ r1_tsep_1(X10653,X10654)
      | r1_tsep_1(X10654,X10653) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk1268_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l1_struct_0(esk1269_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

fof(c_0_27,plain,(
    ! [X10620,X10621] :
      ( ( ~ r1_tsep_1(X10620,X10621)
        | r1_xboole_0(u1_struct_0(X10620),u1_struct_0(X10621))
        | ~ l1_struct_0(X10621)
        | ~ l1_struct_0(X10620) )
      & ( ~ r1_xboole_0(u1_struct_0(X10620),u1_struct_0(X10621))
        | r1_tsep_1(X10620,X10621)
        | ~ l1_struct_0(X10621)
        | ~ l1_struct_0(X10620) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_28,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tsep_1(esk1268_0,esk1269_0)
    | r1_tsep_1(esk1269_0,esk1268_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_30,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_31,plain,(
    ! [X355,X356] :
      ( v1_xboole_0(X356)
      | ~ r1_tarski(X356,X355)
      | ~ r1_xboole_0(X356,X355) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk1268_0,esk1269_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( k2_struct_0(esk1268_0) = u1_struct_0(esk1268_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k2_struct_0(esk1269_0) = u1_struct_0(esk1269_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_36,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r1_tsep_1(esk1268_0,esk1269_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_26])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk1268_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1268_0),u1_struct_0(esk1269_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_21])])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk1268_0),u1_struct_0(esk1269_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1268_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------

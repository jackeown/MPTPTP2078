%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_1__t55_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:30 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 548 expanded)
%              Number of clauses        :   39 ( 207 expanded)
%              Number of leaves         :   10 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  165 (3086 expanded)
%              Number of equality atoms :   39 ( 755 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t55_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',dt_k3_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',dt_k2_pre_topc)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',d1_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',involutiveness_k3_subset_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t30_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',dt_k1_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',t52_pre_topc)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',fc9_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t55_tops_1.p',projectivity_k1_tops_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( v3_pre_topc(X4,X2)
                       => k1_tops_1(X2,X4) = X4 )
                      & ( k1_tops_1(X1,X3) = X3
                       => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_tops_1])).

fof(c_0_11,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | m1_subset_1(k3_subset_1(X17,X18),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( k1_tops_1(esk1_0,esk3_0) = esk3_0
      | v3_pre_topc(esk4_0,esk2_0) )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | v3_pre_topc(esk4_0,esk2_0) )
    & ( k1_tops_1(esk1_0,esk3_0) = esk3_0
      | k1_tops_1(esk2_0,esk4_0) != esk4_0 )
    & ( ~ v3_pre_topc(esk3_0,esk1_0)
      | k1_tops_1(esk2_0,esk4_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | m1_subset_1(k2_pre_topc(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | k1_tops_1(X11,X12) = k3_subset_1(u1_struct_0(X11),k2_pre_topc(X11,k3_subset_1(u1_struct_0(X11),X12))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_17,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k3_subset_1(X24,k3_subset_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X34,X35] :
      ( ( ~ v3_pre_topc(X35,X34)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X34),X35),X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X34),X35),X34)
        | v3_pre_topc(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(k1_tops_1(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_24,plain,(
    ! [X43,X44] :
      ( ( ~ v4_pre_topc(X44,X43)
        | k2_pre_topc(X43,X44) = X44
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) )
      & ( ~ v2_pre_topc(X43)
        | k2_pre_topc(X43,X44) != X44
        | v4_pre_topc(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_25,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_27,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk4_0))) = k1_tops_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_20])])).

cnf(c_0_28,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk4_0)) = k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk4_0),esk2_0)
    | ~ v3_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_20])])).

cnf(c_0_33,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v3_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_34,plain,(
    ! [X53,X54] :
      ( ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | v3_pre_topc(k1_tops_1(X53,X54),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk4_0)) = k3_subset_1(u1_struct_0(esk2_0),esk4_0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20])]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk4_0))) = k1_tops_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk4_0)) = k3_subset_1(u1_struct_0(esk2_0),esk4_0)
    | k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k3_subset_1(u1_struct_0(esk2_0),esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0
    | k1_tops_1(esk2_0,esk4_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_47,negated_conjecture,
    ( k1_tops_1(esk1_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

fof(c_0_48,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | k1_tops_1(X26,k1_tops_1(X26,X27)) = k1_tops_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0)
    | ~ v3_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk4_0)) = k1_tops_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_15]),c_0_20])])).

cnf(c_0_54,negated_conjecture,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(esk2_0),esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk1_0)
    | k1_tops_1(esk2_0,esk4_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk4_0)))) = k1_tops_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_35]),c_0_53]),c_0_20])])).

cnf(c_0_57,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk4_0)) = k3_subset_1(u1_struct_0(esk2_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( k1_tops_1(esk2_0,esk4_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_50])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_31]),c_0_57]),c_0_44]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------

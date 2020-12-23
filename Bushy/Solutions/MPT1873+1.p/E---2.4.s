%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t41_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:32 EDT 2019

% Result     : Theorem 245.37s
% Output     : CNFRefutation 245.37s
% Verified   : 
% Statistics : Number of formulae       :  112 (3701 expanded)
%              Number of clauses        :   81 (1465 expanded)
%              Number of leaves         :   15 ( 902 expanded)
%              Depth                    :   21
%              Number of atoms          :  307 (20446 expanded)
%              Number of equality atoms :   39 (3000 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t41_tex_2)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',dt_k9_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t3_subset)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',redefinition_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',commutativity_k3_xboole_0)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',commutativity_k9_subset_1)).

fof(d6_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',d6_tex_2)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',fc1_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',dt_k2_pre_topc)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t17_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',d10_xboole_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t19_xboole_1)).

fof(t31_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t31_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t48_pre_topc)).

fof(t26_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t41_tex_2.p',t26_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tex_2(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r1_tarski(X3,X2)
                   => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_tex_2])).

fof(c_0_16,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X26))
      | m1_subset_1(k9_subset_1(X26,X27,X28),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_17,negated_conjecture,(
    ! [X8] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v2_tex_2(esk2_0,esk1_0) )
      & ( r1_tarski(esk3_0,esk2_0)
        | ~ v2_tex_2(esk2_0,esk1_0) )
      & ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,esk3_0)) != esk3_0
        | ~ v2_tex_2(esk2_0,esk1_0) )
      & ( v2_tex_2(esk2_0,esk1_0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r1_tarski(X8,esk2_0)
        | k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,X8)) = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_18,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k9_subset_1(X42,X43,X44) = k3_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k3_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

fof(c_0_27,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X15) = k9_subset_1(X13,X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk2_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X18,X19,X20,X23] :
      ( ( m1_subset_1(esk4_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r1_tarski(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( v4_pre_topc(esk4_3(X18,X19,X20),X18)
        | ~ r1_tarski(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( k9_subset_1(u1_struct_0(X18),X19,esk4_3(X18,X19,X20)) = X20
        | ~ r1_tarski(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk5_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( r1_tarski(esk5_2(X18,X19),X19)
        | v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v4_pre_topc(X23,X18)
        | k9_subset_1(u1_struct_0(X18),X19,X23) != esk5_2(X18,X19)
        | v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).

cnf(c_0_32,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X34,X35] :
      ( ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | v4_pre_topc(k2_pre_topc(X34,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | m1_subset_1(k2_pre_topc(X24,X25),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_37,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk5_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k3_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( r1_tarski(esk5_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk5_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(X1,esk2_0) != esk5_2(esk1_0,esk2_0)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20]),c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,k3_xboole_0(esk2_0,X1)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39]),c_0_42])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k3_xboole_0(esk2_0,X1)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_39])])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,X1)) = X1
    | v2_tex_2(esk2_0,esk1_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_38]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk5_2(esk1_0,esk2_0),esk2_0)
    | v2_tex_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_39])])).

cnf(c_0_52,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | m1_subset_1(esk5_2(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_20]),c_0_39])])).

fof(c_0_53,plain,(
    ! [X45,X46] : r1_tarski(k3_xboole_0(X45,X46),X45) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_54,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,k3_xboole_0(esk2_0,X1))) != esk5_2(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])]),c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk5_2(esk1_0,esk2_0))) = esk5_2(esk1_0,esk2_0)
    | v2_tex_2(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_59,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X47,X48,X49] :
      ( ~ r1_tarski(X47,X48)
      | ~ r1_tarski(X47,X49)
      | r1_tarski(X47,k3_xboole_0(X48,X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk4_3(esk1_0,X1,k3_xboole_0(X2,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k3_xboole_0(X2,esk2_0),X1)
    | ~ v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_39])])).

cnf(c_0_63,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_64,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_30])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    | ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_3(esk1_0,esk2_0,k3_xboole_0(X1,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_20])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_63])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk4_3(esk1_0,esk2_0,k3_xboole_0(X1,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_68])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_75,plain,(
    ! [X58,X59,X60] :
      ( ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X58)))
      | ~ v4_pre_topc(X59,X58)
      | ~ r1_tarski(X60,X59)
      | r1_tarski(k2_pre_topc(X58,X60),X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

cnf(c_0_76,plain,
    ( v4_pre_topc(esk4_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_63])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk4_3(esk1_0,esk2_0,k3_xboole_0(esk2_0,X1)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_30])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_64])])).

cnf(c_0_80,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk4_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_81,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( v4_pre_topc(esk4_3(esk1_0,X1,esk3_0),esk1_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_39])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk4_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk4_3(esk1_0,X1,esk3_0)) = esk3_0
    | ~ r1_tarski(esk3_0,X1)
    | ~ v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_77]),c_0_39])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk3_0),X1)
    | ~ v4_pre_topc(X1,esk1_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_77]),c_0_39])])).

cnf(c_0_86,negated_conjecture,
    ( v4_pre_topc(esk4_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_70]),c_0_63]),c_0_20])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk4_3(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_3(esk1_0,esk2_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_70]),c_0_38]),c_0_30]),c_0_63]),c_0_20])])).

fof(c_0_89,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | r1_tarski(X64,k2_pre_topc(X63,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_90,plain,(
    ! [X52,X53,X54] :
      ( ~ r1_tarski(X52,X53)
      | r1_tarski(k3_xboole_0(X52,X54),k3_xboole_0(X53,X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_xboole_1])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk4_3(esk1_0,esk2_0,esk3_0))
    | ~ r1_tarski(esk3_0,esk4_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_88])).

cnf(c_0_93,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,esk3_0)) != esk3_0
    | ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_95,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk3_0),esk4_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_77])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(X1,esk2_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_70])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_77]),c_0_39])])).

cnf(c_0_100,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk3_0)) != esk3_0
    | ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_38]),c_0_30])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk2_0),k3_xboole_0(X2,u1_struct_0(esk1_0)))
    | ~ r1_tarski(k3_xboole_0(X1,esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_29])).

cnf(c_0_102,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_64])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk3_0),k3_xboole_0(k2_pre_topc(esk1_0,esk3_0),esk4_3(esk1_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_96]),c_0_30])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk3_0,u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_97]),c_0_30])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_30])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk3_0)) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_63])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,k3_xboole_0(X1,X2)),k3_xboole_0(u1_struct_0(esk1_0),k3_xboole_0(X2,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_30]),c_0_30])).

cnf(c_0_108,negated_conjecture,
    ( k3_xboole_0(k2_pre_topc(esk1_0,esk3_0),esk4_3(esk1_0,esk2_0,esk3_0)) = k2_pre_topc(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_103]),c_0_59])])).

cnf(c_0_109,negated_conjecture,
    ( k3_xboole_0(esk3_0,u1_struct_0(esk1_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_104]),c_0_59])])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_105]),c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_30]),c_0_88]),c_0_30]),c_0_109]),c_0_110]),
    [proof]).
%------------------------------------------------------------------------------

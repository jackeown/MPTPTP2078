%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t27_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:29 EDT 2019

% Result     : Timeout 286.04s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  107 ( 779 expanded)
%              Number of clauses        :   74 ( 315 expanded)
%              Number of leaves         :   16 ( 191 expanded)
%              Depth                    :   18
%              Number of atoms          :  365 (3291 expanded)
%              Number of equality atoms :   55 ( 623 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
      <=> u1_pre_topc(X1) = k9_setfam_1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',d1_tdlat_3)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',redefinition_k9_setfam_1)).

fof(t17_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',t17_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',cc1_tdlat_3)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',d10_xboole_0)).

fof(d5_tex_2,axiom,(
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
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',d5_tex_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',redefinition_k9_subset_1)).

fof(t27_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( X2 = u1_struct_0(X1)
           => ( v2_tex_2(X2,X1)
            <=> v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',t27_tex_2)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',t28_xboole_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',dt_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',commutativity_k3_xboole_0)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',d5_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',dt_u1_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',d3_tarski)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t27_tex_2.p',t1_subset)).

fof(c_0_16,plain,(
    ! [X17] :
      ( ( ~ v1_tdlat_3(X17)
        | u1_pre_topc(X17) = k9_setfam_1(u1_struct_0(X17))
        | ~ l1_pre_topc(X17) )
      & ( u1_pre_topc(X17) != k9_setfam_1(u1_struct_0(X17))
        | v1_tdlat_3(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tdlat_3])])])).

fof(c_0_17,plain,(
    ! [X46] : k9_setfam_1(X46) = k1_zfmisc_1(X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_18,plain,(
    ! [X50,X51] :
      ( ( ~ v1_tdlat_3(X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
        | v3_pre_topc(X51,X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( m1_subset_1(esk9_1(X50),k1_zfmisc_1(u1_struct_0(X50)))
        | v1_tdlat_3(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( ~ v3_pre_topc(esk9_1(X50),X50)
        | v1_tdlat_3(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_tdlat_3])])])])])).

fof(c_0_19,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | ~ v1_tdlat_3(X9)
      | v2_pre_topc(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_20,plain,(
    ! [X60,X61] :
      ( ( ~ m1_subset_1(X60,k1_zfmisc_1(X61))
        | r1_tarski(X60,X61) )
      & ( ~ r1_tarski(X60,X61)
        | m1_subset_1(X60,k1_zfmisc_1(X61)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( u1_pre_topc(X1) = k9_setfam_1(u1_struct_0(X1))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X26,X27,X28,X31] :
      ( ( m1_subset_1(esk4_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( v3_pre_topc(esk4_3(X26,X27,X28),X26)
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( k9_subset_1(u1_struct_0(X26),X27,esk4_3(X26,X27,X28)) = X28
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk5_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( r1_tarski(esk5_2(X26,X27),X27)
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v3_pre_topc(X31,X26)
        | k9_subset_1(u1_struct_0(X26),X27,X31) != esk5_2(X26,X27)
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

fof(c_0_25,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X47))
      | k9_subset_1(X47,X48,X49) = k3_xboole_0(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_26,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( u1_pre_topc(X1) = k1_zfmisc_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( X2 = u1_struct_0(X1)
             => ( v2_tex_2(X2,X1)
              <=> v1_tdlat_3(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_tex_2])).

cnf(c_0_32,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk5_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,u1_pre_topc(X2))
    | ~ r1_tarski(X1,u1_struct_0(X2))
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

fof(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & esk2_0 = u1_struct_0(esk1_0)
    & ( ~ v2_tex_2(esk2_0,esk1_0)
      | ~ v1_tdlat_3(esk1_0) )
    & ( v2_tex_2(esk2_0,esk1_0)
      | v1_tdlat_3(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

cnf(c_0_38,plain,
    ( v2_tex_2(X1,X2)
    | k3_xboole_0(X1,X3) != esk5_2(X2,X1)
    | ~ v3_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tdlat_3(X2)
    | ~ m1_subset_1(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_40,plain,
    ( m1_subset_1(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X55,X56] :
      ( ~ r1_tarski(X55,X56)
      | k3_xboole_0(X55,X56) = X55 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( v2_tex_2(X1,X2)
    | k3_xboole_0(X1,X3) != esk5_2(X2,X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_subset_1(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_pre_topc(esk1_0))
    | ~ v1_tdlat_3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | v1_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | m1_subset_1(k9_subset_1(X33,X34,X35),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ v1_tdlat_3(X2)
    | ~ m1_subset_1(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(esk2_0,X1) != esk5_2(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,u1_pre_topc(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42])]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( u1_pre_topc(esk1_0) = k1_zfmisc_1(esk2_0)
    | ~ v1_tdlat_3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_41]),c_0_42])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,u1_struct_0(X2)) = X1
    | ~ v1_tdlat_3(X2)
    | ~ m1_subset_1(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_55,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(esk2_0,X1) != esk5_2(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_47])).

cnf(c_0_57,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = X1
    | ~ v1_tdlat_3(esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_41]),c_0_42])])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(esk2_0,k3_xboole_0(X1,X2)) != esk5_2(esk1_0,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2)
    | ~ v1_tdlat_3(esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_57]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(X1,X2) != esk5_2(esk1_0,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_41])).

cnf(c_0_65,plain,
    ( r1_tarski(esk5_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_66,plain,(
    ! [X24,X25] :
      ( ( ~ v3_pre_topc(X25,X24)
        | r2_hidden(X25,u1_pre_topc(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( ~ r2_hidden(X25,u1_pre_topc(X24))
        | v3_pre_topc(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_68,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk4_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_69,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(X1,esk2_0) != esk5_2(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,esk5_2(X2,X1)) = esk5_2(X2,X1)
    | v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_65]),c_0_59])).

fof(c_0_71,plain,(
    ! [X37] :
      ( ~ l1_pre_topc(X37)
      | m1_subset_1(u1_pre_topc(X37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X37)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_72,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk3_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk3_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_74,plain,(
    ! [X53,X54] :
      ( ~ r2_hidden(X53,X54)
      | m1_subset_1(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_75,plain,
    ( r1_tarski(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk4_3(esk1_0,X1,X2)) = X2
    | ~ r1_tarski(X2,X1)
    | ~ v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_41]),c_0_42])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk4_3(esk1_0,X1,X2),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X2,X1)
    | ~ v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_41]),c_0_42])])).

cnf(c_0_78,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | k3_xboole_0(esk2_0,X1) != esk5_2(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_59])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(X1,esk5_2(esk1_0,X1)) = esk5_2(esk1_0,X1)
    | v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_41]),c_0_42])])).

cnf(c_0_80,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_41]),c_0_42])])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,plain,
    ( k3_xboole_0(u1_struct_0(X1),esk4_3(X1,X2,X3)) = esk4_3(X1,X2,X3)
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_75]),c_0_59])).

cnf(c_0_86,negated_conjecture,
    ( k3_xboole_0(X1,esk4_3(esk1_0,X1,X2)) = X2
    | ~ r1_tarski(X2,X1)
    | ~ v2_tex_2(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_76]),c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_64])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_41]),c_0_42])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(esk3_2(X1,u1_pre_topc(esk1_0)),esk1_0)
    | ~ m1_subset_1(esk3_2(X1,u1_pre_topc(esk1_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X2)
    | m1_subset_1(esk3_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,plain,
    ( v3_pre_topc(esk4_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( esk4_3(esk1_0,esk2_0,X1) = X1
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_64]),c_0_42]),c_0_41]),c_0_64])]),c_0_87])]),c_0_28])).

cnf(c_0_93,plain,
    ( v1_tdlat_3(X1)
    | u1_pre_topc(X1) != k9_setfam_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ v3_pre_topc(esk3_2(k1_zfmisc_1(esk2_0),u1_pre_topc(esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_87]),c_0_41]),c_0_41]),c_0_64]),c_0_42])]),c_0_28])).

cnf(c_0_98,plain,
    ( r1_tarski(esk3_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_90])).

cnf(c_0_99,plain,
    ( v1_tdlat_3(X1)
    | u1_pre_topc(X1) != k1_zfmisc_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_93,c_0_22])).

cnf(c_0_100,negated_conjecture,
    ( u1_pre_topc(esk1_0) = k1_zfmisc_1(esk2_0)
    | ~ r1_tarski(k1_zfmisc_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0)
    | ~ v1_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_103,negated_conjecture,
    ( v1_tdlat_3(esk1_0)
    | u1_pre_topc(esk1_0) != k1_zfmisc_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_41]),c_0_42])])).

cnf(c_0_104,negated_conjecture,
    ( u1_pre_topc(esk1_0) = k1_zfmisc_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_tdlat_3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_87])])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])]),c_0_105]),
    [proof]).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t100_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:58 EDT 2019

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 133 expanded)
%              Number of clauses        :   36 (  54 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  267 ( 526 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',redefinition_k9_subset_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',commutativity_k3_xboole_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',existence_m1_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',dt_u1_pre_topc)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',t1_boole)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',redefinition_k4_subset_1)).

fof(fraenkel_a_2_0_tmap_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_tmap_1(X2,X3))
      <=> ? [X4,X5] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = k4_subset_1(u1_struct_0(X2),X4,k9_subset_1(u1_struct_0(X2),X5,X3))
            & r2_hidden(X4,u1_pre_topc(X2))
            & r2_hidden(X5,u1_pre_topc(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',fraenkel_a_2_0_tmap_1)).

fof(fraenkel_a_2_1_tmap_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_tmap_1(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = k9_subset_1(u1_struct_0(X2),X4,X3)
            & r2_hidden(X4,u1_pre_topc(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',fraenkel_a_2_1_tmap_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',commutativity_k4_subset_1)).

fof(t5_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',t5_pre_topc)).

fof(t100_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(a_2_1_tmap_1(X1,X2),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',t100_tmap_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',d3_tarski)).

fof(d8_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t100_tmap_1.p',d8_tmap_1)).

fof(c_0_16,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X34))
      | m1_subset_1(k9_subset_1(X34,X35,X36),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_17,plain,(
    ! [X66,X67,X68] :
      ( ~ m1_subset_1(X68,k1_zfmisc_1(X66))
      | k9_subset_1(X66,X67,X68) = k3_xboole_0(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_18,plain,(
    ! [X72] : k3_xboole_0(X72,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_19,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_20,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X41] : m1_subset_1(esk6_1(X41),X41) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_27,plain,(
    ! [X80,X81,X82] :
      ( ~ r2_hidden(X80,X81)
      | ~ m1_subset_1(X81,k1_zfmisc_1(X82))
      | m1_subset_1(X80,X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_28,plain,(
    ! [X38] :
      ( ~ l1_pre_topc(X38)
      | m1_subset_1(u1_pre_topc(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_29,plain,(
    ! [X69] : k2_xboole_0(X69,k1_xboole_0) = X69 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_30,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X64,k1_zfmisc_1(X63))
      | ~ m1_subset_1(X65,k1_zfmisc_1(X63))
      | k4_subset_1(X63,X64,X65) = k2_xboole_0(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X43,X44,X45,X48,X49] :
      ( ( m1_subset_1(esk7_3(X43,X44,X45),k1_zfmisc_1(u1_struct_0(X44)))
        | ~ r2_hidden(X43,a_2_0_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) )
      & ( m1_subset_1(esk8_3(X43,X44,X45),k1_zfmisc_1(u1_struct_0(X44)))
        | ~ r2_hidden(X43,a_2_0_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) )
      & ( X43 = k4_subset_1(u1_struct_0(X44),esk7_3(X43,X44,X45),k9_subset_1(u1_struct_0(X44),esk8_3(X43,X44,X45),X45))
        | ~ r2_hidden(X43,a_2_0_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) )
      & ( r2_hidden(esk7_3(X43,X44,X45),u1_pre_topc(X44))
        | ~ r2_hidden(X43,a_2_0_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) )
      & ( r2_hidden(esk8_3(X43,X44,X45),u1_pre_topc(X44))
        | ~ r2_hidden(X43,a_2_0_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) )
      & ( ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X44)))
        | X43 != k4_subset_1(u1_struct_0(X44),X48,k9_subset_1(u1_struct_0(X44),X49,X45))
        | ~ r2_hidden(X48,u1_pre_topc(X44))
        | ~ r2_hidden(X49,u1_pre_topc(X44))
        | r2_hidden(X43,a_2_0_tmap_1(X44,X45))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_tmap_1])])])])])])).

fof(c_0_34,plain,(
    ! [X50,X51,X52,X54] :
      ( ( m1_subset_1(esk9_3(X50,X51,X52),k1_zfmisc_1(u1_struct_0(X51)))
        | ~ r2_hidden(X50,a_2_1_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( X50 = k9_subset_1(u1_struct_0(X51),esk9_3(X50,X51,X52),X52)
        | ~ r2_hidden(X50,a_2_1_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( r2_hidden(esk9_3(X50,X51,X52),u1_pre_topc(X51))
        | ~ r2_hidden(X50,a_2_1_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) )
      & ( ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X51)))
        | X50 != k9_subset_1(u1_struct_0(X51),X54,X52)
        | ~ r2_hidden(X54,u1_pre_topc(X51))
        | r2_hidden(X50,a_2_1_tmap_1(X51,X52))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_tmap_1])])])])])])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k4_subset_1(X14,X15,X16) = k4_subset_1(X14,X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( r2_hidden(X4,a_2_0_tmap_1(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k4_subset_1(u1_struct_0(X2),X1,k9_subset_1(u1_struct_0(X2),X3,X5))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk9_3(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_tmap_1(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),u1_pre_topc(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_tmap_1(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k4_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

fof(c_0_47,plain,(
    ! [X83] :
      ( ~ v2_pre_topc(X83)
      | ~ l1_pre_topc(X83)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X83)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_tarski(a_2_1_tmap_1(X1,X2),k5_tmap_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t100_tmap_1])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,a_2_0_tmap_1(X2,X3))
    | v2_struct_0(X2)
    | X1 != k4_subset_1(u1_struct_0(X2),X4,X5)
    | ~ r2_hidden(X5,a_2_1_tmap_1(X2,X3))
    | ~ r2_hidden(X4,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_43]),c_0_44])).

cnf(c_0_50,plain,
    ( k4_subset_1(X1,k1_xboole_0,X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40])])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_tmap_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_42])).

cnf(c_0_52,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(X22,X20)
        | r2_hidden(X22,X21) )
      & ( r2_hidden(esk3_2(X23,X24),X23)
        | r1_tarski(X23,X24) )
      & ( ~ r2_hidden(esk3_2(X23,X24),X24)
        | r1_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(a_2_1_tmap_1(esk1_0,esk2_0),k5_tmap_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_48])])])])).

fof(c_0_55,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | k5_tmap_1(X26,X27) = a_2_0_tmap_1(X26,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tmap_1])])])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,a_2_0_tmap_1(X2,X3))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_tmap_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50])]),c_0_51]),c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(a_2_1_tmap_1(esk1_0,esk2_0),k5_tmap_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( r2_hidden(esk3_2(a_2_1_tmap_1(X1,X2),X3),a_2_0_tmap_1(X1,X2))
    | r1_tarski(a_2_1_tmap_1(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(a_2_1_tmap_1(esk1_0,esk2_0),a_2_0_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_62])]),c_0_63])).

cnf(c_0_67,plain,
    ( r1_tarski(a_2_1_tmap_1(X1,X2),a_2_0_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_60]),c_0_61]),c_0_62])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------

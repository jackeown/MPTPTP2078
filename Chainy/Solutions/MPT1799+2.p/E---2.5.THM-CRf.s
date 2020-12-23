%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1799+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 28.85s
% Output     : CNFRefutation 28.85s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 180 expanded)
%              Number of clauses        :   30 (  62 expanded)
%              Number of leaves         :    9 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  263 (1158 expanded)
%              Number of equality atoms :   34 ( 115 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
             => ( u1_struct_0(X3) = u1_struct_0(X2)
               => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                  & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_tmap_1)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(t105_tmap_1,axiom,(
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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
               => ( u1_struct_0(X3) = u1_struct_0(X2)
                 => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                    & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_tmap_1])).

fof(c_0_10,plain,(
    ! [X10927,X10928] :
      ( ~ l1_pre_topc(X10927)
      | ~ m1_pre_topc(X10928,X10927)
      | r1_tarski(u1_struct_0(X10928),u1_struct_0(X10927)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1267_0)
    & v2_pre_topc(esk1267_0)
    & l1_pre_topc(esk1267_0)
    & ~ v2_struct_0(esk1268_0)
    & m1_pre_topc(esk1268_0,esk1267_0)
    & m1_pre_topc(esk1269_0,k8_tmap_1(esk1267_0,esk1268_0))
    & u1_struct_0(esk1269_0) = u1_struct_0(esk1268_0)
    & ( ~ v1_tsep_1(esk1269_0,k8_tmap_1(esk1267_0,esk1268_0))
      | ~ m1_pre_topc(esk1269_0,k8_tmap_1(esk1267_0,esk1268_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk1268_0,esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X10815,X10816,X10817] :
      ( ( ~ v1_tsep_1(X10816,X10815)
        | ~ m1_pre_topc(X10816,X10815)
        | v3_pre_topc(X10817,X10815)
        | X10817 != u1_struct_0(X10816)
        | ~ m1_subset_1(X10817,k1_zfmisc_1(u1_struct_0(X10815)))
        | ~ m1_pre_topc(X10816,X10815)
        | ~ v2_pre_topc(X10815)
        | ~ l1_pre_topc(X10815) )
      & ( v1_tsep_1(X10816,X10815)
        | ~ v3_pre_topc(X10817,X10815)
        | X10817 != u1_struct_0(X10816)
        | ~ m1_subset_1(X10817,k1_zfmisc_1(u1_struct_0(X10815)))
        | ~ m1_pre_topc(X10816,X10815)
        | ~ v2_pre_topc(X10815)
        | ~ l1_pre_topc(X10815) )
      & ( m1_pre_topc(X10816,X10815)
        | ~ v3_pre_topc(X10817,X10815)
        | X10817 != u1_struct_0(X10816)
        | ~ m1_subset_1(X10817,k1_zfmisc_1(u1_struct_0(X10815)))
        | ~ m1_pre_topc(X10816,X10815)
        | ~ v2_pre_topc(X10815)
        | ~ l1_pre_topc(X10815) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_17,plain,(
    ! [X10841,X10842] :
      ( ~ l1_pre_topc(X10841)
      | ~ m1_pre_topc(X10842,X10841)
      | m1_subset_1(u1_struct_0(X10842),k1_zfmisc_1(u1_struct_0(X10841))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_18,plain,(
    ! [X10696,X10697] :
      ( ( v1_pre_topc(k8_tmap_1(X10696,X10697))
        | v2_struct_0(X10696)
        | ~ v2_pre_topc(X10696)
        | ~ l1_pre_topc(X10696)
        | ~ m1_pre_topc(X10697,X10696) )
      & ( v2_pre_topc(k8_tmap_1(X10696,X10697))
        | v2_struct_0(X10696)
        | ~ v2_pre_topc(X10696)
        | ~ l1_pre_topc(X10696)
        | ~ m1_pre_topc(X10697,X10696) )
      & ( l1_pre_topc(k8_tmap_1(X10696,X10697))
        | v2_struct_0(X10696)
        | ~ v2_pre_topc(X10696)
        | ~ l1_pre_topc(X10696)
        | ~ m1_pre_topc(X10697,X10696) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_19,plain,(
    ! [X10611,X10612,X10613,X10614] :
      ( ( X10613 != k8_tmap_1(X10611,X10612)
        | ~ m1_subset_1(X10614,k1_zfmisc_1(u1_struct_0(X10611)))
        | X10614 != u1_struct_0(X10612)
        | X10613 = k6_tmap_1(X10611,X10614)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) )
      & ( m1_subset_1(esk1254_3(X10611,X10612,X10613),k1_zfmisc_1(u1_struct_0(X10611)))
        | X10613 = k8_tmap_1(X10611,X10612)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) )
      & ( esk1254_3(X10611,X10612,X10613) = u1_struct_0(X10612)
        | X10613 = k8_tmap_1(X10611,X10612)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) )
      & ( X10613 != k6_tmap_1(X10611,esk1254_3(X10611,X10612,X10613))
        | X10613 = k8_tmap_1(X10611,X10612)
        | ~ v1_pre_topc(X10613)
        | ~ v2_pre_topc(X10613)
        | ~ l1_pre_topc(X10613)
        | ~ m1_pre_topc(X10612,X10611)
        | v2_struct_0(X10611)
        | ~ v2_pre_topc(X10611)
        | ~ l1_pre_topc(X10611) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_20,plain,(
    ! [X10757,X10758,X10759] :
      ( v2_struct_0(X10757)
      | ~ v2_pre_topc(X10757)
      | ~ l1_pre_topc(X10757)
      | ~ m1_subset_1(X10758,k1_zfmisc_1(u1_struct_0(X10757)))
      | ~ m1_subset_1(X10759,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X10757,X10758))))
      | X10759 != X10758
      | v3_pre_topc(X10759,k6_tmap_1(X10757,X10758)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

fof(c_0_21,plain,(
    ! [X10755,X10756] :
      ( ( u1_struct_0(k6_tmap_1(X10755,X10756)) = u1_struct_0(X10755)
        | ~ m1_subset_1(X10756,k1_zfmisc_1(u1_struct_0(X10755)))
        | v2_struct_0(X10755)
        | ~ v2_pre_topc(X10755)
        | ~ l1_pre_topc(X10755) )
      & ( u1_pre_topc(k6_tmap_1(X10755,X10756)) = k5_tmap_1(X10755,X10756)
        | ~ m1_subset_1(X10756,k1_zfmisc_1(u1_struct_0(X10755)))
        | v2_struct_0(X10755)
        | ~ v2_pre_topc(X10755)
        | ~ l1_pre_topc(X10755) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1268_0),u1_struct_0(esk1267_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_24,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1267_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_tsep_1(esk1269_0,k8_tmap_1(esk1267_0,esk1268_0))
    | ~ m1_pre_topc(esk1269_0,k8_tmap_1(esk1267_0,esk1268_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk1269_0,k8_tmap_1(esk1267_0,esk1268_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1268_0),k1_zfmisc_1(u1_struct_0(esk1267_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_37,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk1269_0) = u1_struct_0(esk1268_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk1267_0,esk1268_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_27]),c_0_15])]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk1267_0,esk1268_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_27]),c_0_15])]),c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_tsep_1(esk1269_0,k8_tmap_1(esk1267_0,esk1268_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_42,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])]),c_0_25]),c_0_29]),c_0_33]),c_0_26])).

cnf(c_0_43,plain,
    ( v3_pre_topc(X1,k6_tmap_1(X2,X1))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk1267_0,u1_struct_0(esk1268_0))) = u1_struct_0(esk1267_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_27]),c_0_15])]),c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk1268_0),k8_tmap_1(esk1267_0,esk1268_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k8_tmap_1(esk1267_0,esk1268_0) = k6_tmap_1(esk1267_0,u1_struct_0(esk1268_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14]),c_0_27]),c_0_15])]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk1268_0),k6_tmap_1(esk1267_0,u1_struct_0(esk1268_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_27]),c_0_15]),c_0_44]),c_0_36])]),c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------

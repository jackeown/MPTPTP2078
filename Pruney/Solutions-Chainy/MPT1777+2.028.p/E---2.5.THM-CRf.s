%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:00 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 468 expanded)
%              Number of clauses        :   62 ( 170 expanded)
%              Number of leaves         :   18 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  409 (4544 expanded)
%              Number of equality atoms :   23 ( 446 expanded)
%              Maximal formula depth    :   33 (   5 average)
%              Maximal clause size      :   46 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                 => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t84_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( v3_pre_topc(X6,X4)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X2,X5,X7)
                                      <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                   => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tmap_1])).

fof(c_0_19,plain,(
    ! [X134,X135] :
      ( ~ l1_pre_topc(X134)
      | ~ m1_pre_topc(X135,X134)
      | l1_pre_topc(X135) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk50_0)
    & v2_pre_topc(esk50_0)
    & l1_pre_topc(esk50_0)
    & ~ v2_struct_0(esk51_0)
    & v2_pre_topc(esk51_0)
    & l1_pre_topc(esk51_0)
    & ~ v2_struct_0(esk52_0)
    & m1_pre_topc(esk52_0,esk50_0)
    & ~ v2_struct_0(esk53_0)
    & m1_pre_topc(esk53_0,esk50_0)
    & v1_funct_1(esk54_0)
    & v1_funct_2(esk54_0,u1_struct_0(esk53_0),u1_struct_0(esk51_0))
    & m1_subset_1(esk54_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk53_0),u1_struct_0(esk51_0))))
    & g1_pre_topc(u1_struct_0(esk52_0),u1_pre_topc(esk52_0)) = esk53_0
    & m1_subset_1(esk55_0,u1_struct_0(esk53_0))
    & m1_subset_1(esk56_0,u1_struct_0(esk52_0))
    & esk55_0 = esk56_0
    & r1_tmap_1(esk52_0,esk51_0,k3_tmap_1(esk50_0,esk51_0,esk53_0,esk52_0,esk54_0),esk56_0)
    & ~ r1_tmap_1(esk53_0,esk51_0,esk54_0,esk55_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_21,plain,(
    ! [X160,X161] :
      ( ~ l1_pre_topc(X160)
      | ~ m1_pre_topc(X161,g1_pre_topc(u1_struct_0(X160),u1_pre_topc(X160)))
      | m1_pre_topc(X161,X160) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk52_0,esk50_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk50_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X216,X217,X218] :
      ( ( ~ r1_tarski(u1_struct_0(X217),u1_struct_0(X218))
        | m1_pre_topc(X217,X218)
        | ~ m1_pre_topc(X218,X216)
        | ~ m1_pre_topc(X217,X216)
        | ~ v2_pre_topc(X216)
        | ~ l1_pre_topc(X216) )
      & ( ~ m1_pre_topc(X217,X218)
        | r1_tarski(u1_struct_0(X217),u1_struct_0(X218))
        | ~ m1_pre_topc(X218,X216)
        | ~ m1_pre_topc(X217,X216)
        | ~ v2_pre_topc(X216)
        | ~ l1_pre_topc(X216) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk52_0),u1_pre_topc(esk52_0)) = esk53_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk52_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

fof(c_0_30,plain,(
    ! [X208] :
      ( ~ l1_pre_topc(X208)
      | m1_pre_topc(X208,X208) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk53_0,esk50_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,plain,(
    ! [X174,X175] :
      ( ( ~ m1_pre_topc(X174,X175)
        | m1_pre_topc(X174,g1_pre_topc(u1_struct_0(X175),u1_pre_topc(X175)))
        | ~ l1_pre_topc(X175)
        | ~ l1_pre_topc(X174) )
      & ( ~ m1_pre_topc(X174,g1_pre_topc(u1_struct_0(X175),u1_pre_topc(X175)))
        | m1_pre_topc(X174,X175)
        | ~ l1_pre_topc(X175)
        | ~ l1_pre_topc(X174) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

cnf(c_0_33,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk50_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X209,X210] :
      ( ~ l1_pre_topc(X209)
      | ~ m1_pre_topc(X210,X209)
      | r1_tarski(u1_struct_0(X210),u1_struct_0(X209)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(X1,esk52_0)
    | ~ m1_pre_topc(X1,esk53_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_38,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk53_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_31]),c_0_24])])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(X1,esk52_0)
    | ~ m1_pre_topc(X1,esk50_0)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(esk52_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_24]),c_0_34])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk53_0,esk52_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_45,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk52_0,esk52_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_42])])).

fof(c_0_47,plain,(
    ! [X235,X236,X237,X238,X239,X240,X241,X242] :
      ( ( ~ r1_tmap_1(X238,X236,X239,X241)
        | r1_tmap_1(X237,X236,k3_tmap_1(X235,X236,X238,X237,X239),X242)
        | ~ v3_pre_topc(X240,X238)
        | ~ r2_hidden(X241,X240)
        | ~ r1_tarski(X240,u1_struct_0(X237))
        | X241 != X242
        | ~ m1_subset_1(X242,u1_struct_0(X237))
        | ~ m1_subset_1(X241,u1_struct_0(X238))
        | ~ m1_subset_1(X240,k1_zfmisc_1(u1_struct_0(X238)))
        | ~ m1_pre_topc(X237,X238)
        | ~ v1_funct_1(X239)
        | ~ v1_funct_2(X239,u1_struct_0(X238),u1_struct_0(X236))
        | ~ m1_subset_1(X239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X238),u1_struct_0(X236))))
        | v2_struct_0(X238)
        | ~ m1_pre_topc(X238,X235)
        | v2_struct_0(X237)
        | ~ m1_pre_topc(X237,X235)
        | v2_struct_0(X236)
        | ~ v2_pre_topc(X236)
        | ~ l1_pre_topc(X236)
        | v2_struct_0(X235)
        | ~ v2_pre_topc(X235)
        | ~ l1_pre_topc(X235) )
      & ( ~ r1_tmap_1(X237,X236,k3_tmap_1(X235,X236,X238,X237,X239),X242)
        | r1_tmap_1(X238,X236,X239,X241)
        | ~ v3_pre_topc(X240,X238)
        | ~ r2_hidden(X241,X240)
        | ~ r1_tarski(X240,u1_struct_0(X237))
        | X241 != X242
        | ~ m1_subset_1(X242,u1_struct_0(X237))
        | ~ m1_subset_1(X241,u1_struct_0(X238))
        | ~ m1_subset_1(X240,k1_zfmisc_1(u1_struct_0(X238)))
        | ~ m1_pre_topc(X237,X238)
        | ~ v1_funct_1(X239)
        | ~ v1_funct_2(X239,u1_struct_0(X238),u1_struct_0(X236))
        | ~ m1_subset_1(X239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X238),u1_struct_0(X236))))
        | v2_struct_0(X238)
        | ~ m1_pre_topc(X238,X235)
        | v2_struct_0(X237)
        | ~ m1_pre_topc(X237,X235)
        | v2_struct_0(X236)
        | ~ v2_pre_topc(X236)
        | ~ l1_pre_topc(X236)
        | v2_struct_0(X235)
        | ~ v2_pre_topc(X235)
        | ~ l1_pre_topc(X235) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).

fof(c_0_48,plain,(
    ! [X51,X52,X53] :
      ( ~ r2_hidden(X51,X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(X53))
      | m1_subset_1(X51,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_49,plain,(
    ! [X224,X225,X226] :
      ( ~ v2_pre_topc(X224)
      | ~ l1_pre_topc(X224)
      | ~ m1_pre_topc(X225,X224)
      | ~ m1_pre_topc(X226,X225)
      | m1_pre_topc(X226,X224) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk53_0),u1_struct_0(esk52_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_29])])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk52_0,esk53_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28]),c_0_29])])).

fof(c_0_53,plain,(
    ! [X142] :
      ( v2_struct_0(X142)
      | ~ l1_struct_0(X142)
      | ~ v1_xboole_0(k2_struct_0(X142)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

fof(c_0_54,plain,(
    ! [X131] :
      ( ~ l1_struct_0(X131)
      | k2_struct_0(X131) = u1_struct_0(X131) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_55,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_56,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | ~ v3_pre_topc(X8,X4)
    | ~ r2_hidden(X7,X8)
    | ~ r1_tarski(X8,u1_struct_0(X1))
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk52_0,esk51_0,k3_tmap_1(esk50_0,esk51_0,esk53_0,esk52_0,esk54_0),esk56_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( esk55_0 = esk56_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk52_0) = u1_struct_0(esk53_0)
    | ~ r1_tarski(u1_struct_0(esk52_0),u1_struct_0(esk53_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk52_0),u1_struct_0(esk53_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_52]),c_0_39])])).

fof(c_0_63,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X49,k1_zfmisc_1(X50))
        | r1_tarski(X49,X50) )
      & ( ~ r1_tarski(X49,X50)
        | m1_subset_1(X49,k1_zfmisc_1(X50)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_64,plain,(
    ! [X127,X128] :
      ( ~ v2_pre_topc(X127)
      | ~ l1_pre_topc(X127)
      | ~ m1_pre_topc(X128,X127)
      | v2_pre_topc(X128) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk55_0,u1_struct_0(esk53_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_69,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v3_pre_topc(X7,X1)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ r1_tarski(X7,u1_struct_0(X6))
    | ~ r2_hidden(X4,X7) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tmap_1(esk52_0,esk51_0,k3_tmap_1(esk50_0,esk51_0,esk53_0,esk52_0,esk54_0),esk55_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( l1_pre_topc(esk51_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( v2_pre_topc(esk51_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(esk54_0,u1_struct_0(esk53_0),u1_struct_0(esk51_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(esk54_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk54_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk53_0),u1_struct_0(esk51_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk52_0) = u1_struct_0(esk53_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tmap_1(esk53_0,esk51_0,esk54_0,esk55_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_struct_0(esk52_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_struct_0(esk51_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_80,negated_conjecture,
    ( ~ v2_struct_0(esk50_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_81,negated_conjecture,
    ( ~ v2_struct_0(esk53_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_83,plain,(
    ! [X184] :
      ( ~ v2_pre_topc(X184)
      | ~ l1_pre_topc(X184)
      | v3_pre_topc(k2_struct_0(X184),X184) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

cnf(c_0_84,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk53_0))
    | r2_hidden(esk55_0,u1_struct_0(esk53_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_87,plain,(
    ! [X133] :
      ( ~ l1_pre_topc(X133)
      | l1_struct_0(X133) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk53_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk53_0)))
    | ~ r2_hidden(esk55_0,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_31]),c_0_52]),c_0_24]),c_0_71]),c_0_34]),c_0_72]),c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_68]),c_0_76])]),c_0_77]),c_0_78]),c_0_79]),c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_89,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( v2_pre_topc(esk53_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_31]),c_0_24]),c_0_34])])).

cnf(c_0_91,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk55_0,u1_struct_0(esk53_0))
    | ~ l1_struct_0(esk53_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_81])).

cnf(c_0_93,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(esk53_0),k1_zfmisc_1(u1_struct_0(esk53_0)))
    | ~ r2_hidden(esk55_0,k2_struct_0(esk53_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_39]),c_0_90])])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_42])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk55_0,u1_struct_0(esk53_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_39])])).

cnf(c_0_97,negated_conjecture,
    ( ~ l1_struct_0(esk53_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_66]),c_0_95]),c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_93]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:15:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S4d
% 0.18/0.50  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.50  #
% 0.18/0.50  # Preprocessing time       : 0.044 s
% 0.18/0.50  # Presaturation interreduction done
% 0.18/0.50  
% 0.18/0.50  # Proof found!
% 0.18/0.50  # SZS status Theorem
% 0.18/0.50  # SZS output start CNFRefutation
% 0.18/0.50  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.18/0.50  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.50  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.18/0.50  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.18/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.50  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.18/0.50  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.18/0.50  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.18/0.50  fof(t84_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.18/0.50  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.18/0.50  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.18/0.50  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.18/0.50  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.18/0.50  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.18/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.50  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.18/0.50  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.18/0.50  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.50  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.18/0.50  fof(c_0_19, plain, ![X134, X135]:(~l1_pre_topc(X134)|(~m1_pre_topc(X135,X134)|l1_pre_topc(X135))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.50  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk50_0)&v2_pre_topc(esk50_0))&l1_pre_topc(esk50_0))&(((~v2_struct_0(esk51_0)&v2_pre_topc(esk51_0))&l1_pre_topc(esk51_0))&((~v2_struct_0(esk52_0)&m1_pre_topc(esk52_0,esk50_0))&((~v2_struct_0(esk53_0)&m1_pre_topc(esk53_0,esk50_0))&(((v1_funct_1(esk54_0)&v1_funct_2(esk54_0,u1_struct_0(esk53_0),u1_struct_0(esk51_0)))&m1_subset_1(esk54_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk53_0),u1_struct_0(esk51_0)))))&(g1_pre_topc(u1_struct_0(esk52_0),u1_pre_topc(esk52_0))=esk53_0&(m1_subset_1(esk55_0,u1_struct_0(esk53_0))&(m1_subset_1(esk56_0,u1_struct_0(esk52_0))&((esk55_0=esk56_0&r1_tmap_1(esk52_0,esk51_0,k3_tmap_1(esk50_0,esk51_0,esk53_0,esk52_0,esk54_0),esk56_0))&~r1_tmap_1(esk53_0,esk51_0,esk54_0,esk55_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.18/0.50  fof(c_0_21, plain, ![X160, X161]:(~l1_pre_topc(X160)|(~m1_pre_topc(X161,g1_pre_topc(u1_struct_0(X160),u1_pre_topc(X160)))|m1_pre_topc(X161,X160))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.18/0.50  cnf(c_0_22, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.50  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk52_0,esk50_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk50_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  fof(c_0_25, plain, ![X216, X217, X218]:((~r1_tarski(u1_struct_0(X217),u1_struct_0(X218))|m1_pre_topc(X217,X218)|~m1_pre_topc(X218,X216)|~m1_pre_topc(X217,X216)|(~v2_pre_topc(X216)|~l1_pre_topc(X216)))&(~m1_pre_topc(X217,X218)|r1_tarski(u1_struct_0(X217),u1_struct_0(X218))|~m1_pre_topc(X218,X216)|~m1_pre_topc(X217,X216)|(~v2_pre_topc(X216)|~l1_pre_topc(X216)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.18/0.50  fof(c_0_26, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.50  cnf(c_0_27, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.50  cnf(c_0_28, negated_conjecture, (g1_pre_topc(u1_struct_0(esk52_0),u1_pre_topc(esk52_0))=esk53_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk52_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.18/0.50  fof(c_0_30, plain, ![X208]:(~l1_pre_topc(X208)|m1_pre_topc(X208,X208)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.18/0.50  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk53_0,esk50_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  fof(c_0_32, plain, ![X174, X175]:((~m1_pre_topc(X174,X175)|m1_pre_topc(X174,g1_pre_topc(u1_struct_0(X175),u1_pre_topc(X175)))|~l1_pre_topc(X175)|~l1_pre_topc(X174))&(~m1_pre_topc(X174,g1_pre_topc(u1_struct_0(X175),u1_pre_topc(X175)))|m1_pre_topc(X174,X175)|~l1_pre_topc(X175)|~l1_pre_topc(X174))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.18/0.50  cnf(c_0_33, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.50  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk50_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_35, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.50  fof(c_0_36, plain, ![X209, X210]:(~l1_pre_topc(X209)|(~m1_pre_topc(X210,X209)|r1_tarski(u1_struct_0(X210),u1_struct_0(X209)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.18/0.50  cnf(c_0_37, negated_conjecture, (m1_pre_topc(X1,esk52_0)|~m1_pre_topc(X1,esk53_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.18/0.50  cnf(c_0_38, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.50  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk53_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_31]), c_0_24])])).
% 0.18/0.50  cnf(c_0_40, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.50  cnf(c_0_41, negated_conjecture, (m1_pre_topc(X1,esk52_0)|~m1_pre_topc(X1,esk50_0)|~r1_tarski(u1_struct_0(X1),u1_struct_0(esk52_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_24]), c_0_34])])).
% 0.18/0.50  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_35])).
% 0.18/0.50  cnf(c_0_43, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.50  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk53_0,esk52_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.18/0.50  cnf(c_0_45, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_40, c_0_22])).
% 0.18/0.50  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk52_0,esk52_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_42])])).
% 0.18/0.50  fof(c_0_47, plain, ![X235, X236, X237, X238, X239, X240, X241, X242]:((~r1_tmap_1(X238,X236,X239,X241)|r1_tmap_1(X237,X236,k3_tmap_1(X235,X236,X238,X237,X239),X242)|(~v3_pre_topc(X240,X238)|~r2_hidden(X241,X240)|~r1_tarski(X240,u1_struct_0(X237))|X241!=X242)|~m1_subset_1(X242,u1_struct_0(X237))|~m1_subset_1(X241,u1_struct_0(X238))|~m1_subset_1(X240,k1_zfmisc_1(u1_struct_0(X238)))|~m1_pre_topc(X237,X238)|(~v1_funct_1(X239)|~v1_funct_2(X239,u1_struct_0(X238),u1_struct_0(X236))|~m1_subset_1(X239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X238),u1_struct_0(X236)))))|(v2_struct_0(X238)|~m1_pre_topc(X238,X235))|(v2_struct_0(X237)|~m1_pre_topc(X237,X235))|(v2_struct_0(X236)|~v2_pre_topc(X236)|~l1_pre_topc(X236))|(v2_struct_0(X235)|~v2_pre_topc(X235)|~l1_pre_topc(X235)))&(~r1_tmap_1(X237,X236,k3_tmap_1(X235,X236,X238,X237,X239),X242)|r1_tmap_1(X238,X236,X239,X241)|(~v3_pre_topc(X240,X238)|~r2_hidden(X241,X240)|~r1_tarski(X240,u1_struct_0(X237))|X241!=X242)|~m1_subset_1(X242,u1_struct_0(X237))|~m1_subset_1(X241,u1_struct_0(X238))|~m1_subset_1(X240,k1_zfmisc_1(u1_struct_0(X238)))|~m1_pre_topc(X237,X238)|(~v1_funct_1(X239)|~v1_funct_2(X239,u1_struct_0(X238),u1_struct_0(X236))|~m1_subset_1(X239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X238),u1_struct_0(X236)))))|(v2_struct_0(X238)|~m1_pre_topc(X238,X235))|(v2_struct_0(X237)|~m1_pre_topc(X237,X235))|(v2_struct_0(X236)|~v2_pre_topc(X236)|~l1_pre_topc(X236))|(v2_struct_0(X235)|~v2_pre_topc(X235)|~l1_pre_topc(X235)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).
% 0.18/0.50  fof(c_0_48, plain, ![X51, X52, X53]:(~r2_hidden(X51,X52)|~m1_subset_1(X52,k1_zfmisc_1(X53))|m1_subset_1(X51,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.18/0.50  fof(c_0_49, plain, ![X224, X225, X226]:(~v2_pre_topc(X224)|~l1_pre_topc(X224)|(~m1_pre_topc(X225,X224)|(~m1_pre_topc(X226,X225)|m1_pre_topc(X226,X224)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.18/0.50  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.50  cnf(c_0_51, negated_conjecture, (r1_tarski(u1_struct_0(esk53_0),u1_struct_0(esk52_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_29])])).
% 0.18/0.50  cnf(c_0_52, negated_conjecture, (m1_pre_topc(esk52_0,esk53_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_28]), c_0_29])])).
% 0.18/0.50  fof(c_0_53, plain, ![X142]:(v2_struct_0(X142)|~l1_struct_0(X142)|~v1_xboole_0(k2_struct_0(X142))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.18/0.50  fof(c_0_54, plain, ![X131]:(~l1_struct_0(X131)|k2_struct_0(X131)=u1_struct_0(X131)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.18/0.50  fof(c_0_55, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.18/0.50  cnf(c_0_56, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~v3_pre_topc(X8,X4)|~r2_hidden(X7,X8)|~r1_tarski(X8,u1_struct_0(X1))|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.50  cnf(c_0_57, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.50  cnf(c_0_58, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.50  cnf(c_0_59, negated_conjecture, (r1_tmap_1(esk52_0,esk51_0,k3_tmap_1(esk50_0,esk51_0,esk53_0,esk52_0,esk54_0),esk56_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_60, negated_conjecture, (esk55_0=esk56_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk52_0)=u1_struct_0(esk53_0)|~r1_tarski(u1_struct_0(esk52_0),u1_struct_0(esk53_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.50  cnf(c_0_62, negated_conjecture, (r1_tarski(u1_struct_0(esk52_0),u1_struct_0(esk53_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_52]), c_0_39])])).
% 0.18/0.50  fof(c_0_63, plain, ![X49, X50]:((~m1_subset_1(X49,k1_zfmisc_1(X50))|r1_tarski(X49,X50))&(~r1_tarski(X49,X50)|m1_subset_1(X49,k1_zfmisc_1(X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.50  fof(c_0_64, plain, ![X127, X128]:(~v2_pre_topc(X127)|~l1_pre_topc(X127)|(~m1_pre_topc(X128,X127)|v2_pre_topc(X128))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.18/0.50  cnf(c_0_65, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.50  cnf(c_0_66, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.50  cnf(c_0_67, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.50  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk55_0,u1_struct_0(esk53_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_69, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v3_pre_topc(X7,X1)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X6))|~r1_tarski(X7,u1_struct_0(X6))|~r2_hidden(X4,X7)), inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.18/0.50  cnf(c_0_70, negated_conjecture, (r1_tmap_1(esk52_0,esk51_0,k3_tmap_1(esk50_0,esk51_0,esk53_0,esk52_0,esk54_0),esk55_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.50  cnf(c_0_71, negated_conjecture, (l1_pre_topc(esk51_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_72, negated_conjecture, (v2_pre_topc(esk51_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_73, negated_conjecture, (v1_funct_2(esk54_0,u1_struct_0(esk53_0),u1_struct_0(esk51_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_74, negated_conjecture, (v1_funct_1(esk54_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk54_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk53_0),u1_struct_0(esk51_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk52_0)=u1_struct_0(esk53_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.18/0.50  cnf(c_0_77, negated_conjecture, (~r1_tmap_1(esk53_0,esk51_0,esk54_0,esk55_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_78, negated_conjecture, (~v2_struct_0(esk52_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_79, negated_conjecture, (~v2_struct_0(esk51_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_80, negated_conjecture, (~v2_struct_0(esk50_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_81, negated_conjecture, (~v2_struct_0(esk53_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.50  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.50  fof(c_0_83, plain, ![X184]:(~v2_pre_topc(X184)|~l1_pre_topc(X184)|v3_pre_topc(k2_struct_0(X184),X184)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.18/0.50  cnf(c_0_84, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.18/0.50  cnf(c_0_85, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.18/0.50  cnf(c_0_86, negated_conjecture, (v1_xboole_0(u1_struct_0(esk53_0))|r2_hidden(esk55_0,u1_struct_0(esk53_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.18/0.50  fof(c_0_87, plain, ![X133]:(~l1_pre_topc(X133)|l1_struct_0(X133)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.50  cnf(c_0_88, negated_conjecture, (~v3_pre_topc(X1,esk53_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk53_0)))|~r2_hidden(esk55_0,X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_31]), c_0_52]), c_0_24]), c_0_71]), c_0_34]), c_0_72]), c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_68]), c_0_76])]), c_0_77]), c_0_78]), c_0_79]), c_0_80]), c_0_81]), c_0_82])).
% 0.18/0.50  cnf(c_0_89, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.18/0.50  cnf(c_0_90, negated_conjecture, (v2_pre_topc(esk53_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_31]), c_0_24]), c_0_34])])).
% 0.18/0.50  cnf(c_0_91, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.50  cnf(c_0_92, negated_conjecture, (r2_hidden(esk55_0,u1_struct_0(esk53_0))|~l1_struct_0(esk53_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_81])).
% 0.18/0.50  cnf(c_0_93, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.18/0.50  cnf(c_0_94, negated_conjecture, (~m1_subset_1(k2_struct_0(esk53_0),k1_zfmisc_1(u1_struct_0(esk53_0)))|~r2_hidden(esk55_0,k2_struct_0(esk53_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_39]), c_0_90])])).
% 0.18/0.50  cnf(c_0_95, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_91, c_0_42])).
% 0.18/0.50  cnf(c_0_96, negated_conjecture, (r2_hidden(esk55_0,u1_struct_0(esk53_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_39])])).
% 0.18/0.50  cnf(c_0_97, negated_conjecture, (~l1_struct_0(esk53_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_66]), c_0_95]), c_0_96])])).
% 0.18/0.50  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_93]), c_0_39])]), ['proof']).
% 0.18/0.50  # SZS output end CNFRefutation
% 0.18/0.50  # Proof object total steps             : 99
% 0.18/0.50  # Proof object clause steps            : 62
% 0.18/0.50  # Proof object formula steps           : 37
% 0.18/0.50  # Proof object conjectures             : 41
% 0.18/0.50  # Proof object clause conjectures      : 38
% 0.18/0.50  # Proof object formula conjectures     : 3
% 0.18/0.50  # Proof object initial clauses used    : 37
% 0.18/0.50  # Proof object initial formulas used   : 18
% 0.18/0.50  # Proof object generating inferences   : 20
% 0.18/0.50  # Proof object simplifying inferences  : 61
% 0.18/0.50  # Training examples: 0 positive, 0 negative
% 0.18/0.50  # Parsed axioms                        : 113
% 0.18/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.50  # Initial clauses                      : 311
% 0.18/0.50  # Removed in clause preprocessing      : 12
% 0.18/0.50  # Initial clauses in saturation        : 299
% 0.18/0.50  # Processed clauses                    : 1423
% 0.18/0.50  # ...of these trivial                  : 22
% 0.18/0.50  # ...subsumed                          : 400
% 0.18/0.50  # ...remaining for further processing  : 1001
% 0.18/0.50  # Other redundant clauses eliminated   : 24
% 0.18/0.50  # Clauses deleted for lack of memory   : 0
% 0.18/0.50  # Backward-subsumed                    : 5
% 0.18/0.50  # Backward-rewritten                   : 97
% 0.18/0.50  # Generated clauses                    : 2215
% 0.18/0.50  # ...of the previous two non-trivial   : 1980
% 0.18/0.50  # Contextual simplify-reflections      : 23
% 0.18/0.50  # Paramodulations                      : 2189
% 0.18/0.50  # Factorizations                       : 0
% 0.18/0.50  # Equation resolutions                 : 27
% 0.18/0.50  # Propositional unsat checks           : 0
% 0.18/0.50  #    Propositional check models        : 0
% 0.18/0.50  #    Propositional check unsatisfiable : 0
% 0.18/0.50  #    Propositional clauses             : 0
% 0.18/0.50  #    Propositional clauses after purity: 0
% 0.18/0.50  #    Propositional unsat core size     : 0
% 0.18/0.50  #    Propositional preprocessing time  : 0.000
% 0.18/0.50  #    Propositional encoding time       : 0.000
% 0.18/0.50  #    Propositional solver time         : 0.000
% 0.18/0.50  #    Success case prop preproc time    : 0.000
% 0.18/0.50  #    Success case prop encoding time   : 0.000
% 0.18/0.50  #    Success case prop solver time     : 0.000
% 0.18/0.50  # Current number of processed clauses  : 638
% 0.18/0.50  #    Positive orientable unit clauses  : 205
% 0.18/0.50  #    Positive unorientable unit clauses: 0
% 0.18/0.50  #    Negative unit clauses             : 76
% 0.18/0.50  #    Non-unit-clauses                  : 357
% 0.18/0.50  # Current number of unprocessed clauses: 1031
% 0.18/0.50  # ...number of literals in the above   : 4709
% 0.18/0.50  # Current number of archived formulas  : 0
% 0.18/0.50  # Current number of archived clauses   : 340
% 0.18/0.50  # Clause-clause subsumption calls (NU) : 78745
% 0.18/0.50  # Rec. Clause-clause subsumption calls : 15317
% 0.18/0.50  # Non-unit clause-clause subsumptions  : 153
% 0.18/0.50  # Unit Clause-clause subsumption calls : 3874
% 0.18/0.50  # Rewrite failures with RHS unbound    : 0
% 0.18/0.50  # BW rewrite match attempts            : 75
% 0.18/0.50  # BW rewrite match successes           : 17
% 0.18/0.50  # Condensation attempts                : 0
% 0.18/0.50  # Condensation successes               : 0
% 0.18/0.50  # Termbank termtop insertions          : 67698
% 0.18/0.50  
% 0.18/0.50  # -------------------------------------------------
% 0.18/0.50  # User time                : 0.157 s
% 0.18/0.50  # System time              : 0.008 s
% 0.18/0.50  # Total time               : 0.165 s
% 0.18/0.50  # Maximum resident set size: 1752 pages
%------------------------------------------------------------------------------

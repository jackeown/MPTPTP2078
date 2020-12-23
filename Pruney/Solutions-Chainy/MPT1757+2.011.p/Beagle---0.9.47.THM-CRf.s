%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:05 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 834 expanded)
%              Number of leaves         :   43 ( 333 expanded)
%              Depth                    :   20
%              Number of atoms          :  475 (6268 expanded)
%              Number of equality atoms :    5 ( 299 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_310,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_180,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_173,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( m1_connsp_2(C,A,B)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( m1_connsp_2(D,A,B)
                          & v3_pre_topc(D,A)
                          & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_267,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_220,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_81,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_52,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_36,plain,(
    ! [B_58,A_56] :
      ( m1_subset_1(u1_struct_0(B_58),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_pre_topc(B_58,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_195,plain,(
    ! [B_347,A_348] :
      ( v3_pre_topc(u1_struct_0(B_347),A_348)
      | ~ v1_tsep_1(B_347,A_348)
      | ~ m1_subset_1(u1_struct_0(B_347),k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ m1_pre_topc(B_347,A_348)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_199,plain,(
    ! [B_58,A_56] :
      ( v3_pre_topc(u1_struct_0(B_58),A_56)
      | ~ v1_tsep_1(B_58,A_56)
      | ~ v2_pre_topc(A_56)
      | ~ m1_pre_topc(B_58,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_36,c_195])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_287,plain,(
    ! [A_363,B_364,C_365] :
      ( r1_tarski('#skF_1'(A_363,B_364,C_365),C_365)
      | ~ m1_connsp_2(C_365,A_363,B_364)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ m1_subset_1(B_364,u1_struct_0(A_363))
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_305,plain,(
    ! [A_56,B_364,B_58] :
      ( r1_tarski('#skF_1'(A_56,B_364,u1_struct_0(B_58)),u1_struct_0(B_58))
      | ~ m1_connsp_2(u1_struct_0(B_58),A_56,B_364)
      | ~ m1_subset_1(B_364,u1_struct_0(A_56))
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56)
      | ~ m1_pre_topc(B_58,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_36,c_287])).

tff(c_26,plain,(
    ! [A_35,B_43,C_47] :
      ( m1_subset_1('#skF_1'(A_35,B_43,C_47),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_connsp_2(C_47,A_35,B_43)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_43,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_103,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80])).

tff(c_114,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_82])).

tff(c_691,plain,(
    ! [E_432,B_435,G_433,C_437,D_434,A_436] :
      ( r1_tmap_1(B_435,A_436,C_437,G_433)
      | ~ r1_tmap_1(D_434,A_436,k2_tmap_1(B_435,A_436,C_437,D_434),G_433)
      | ~ m1_connsp_2(E_432,B_435,G_433)
      | ~ r1_tarski(E_432,u1_struct_0(D_434))
      | ~ m1_subset_1(G_433,u1_struct_0(D_434))
      | ~ m1_subset_1(G_433,u1_struct_0(B_435))
      | ~ m1_subset_1(E_432,k1_zfmisc_1(u1_struct_0(B_435)))
      | ~ m1_pre_topc(D_434,B_435)
      | v2_struct_0(D_434)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_435),u1_struct_0(A_436))))
      | ~ v1_funct_2(C_437,u1_struct_0(B_435),u1_struct_0(A_436))
      | ~ v1_funct_1(C_437)
      | ~ l1_pre_topc(B_435)
      | ~ v2_pre_topc(B_435)
      | v2_struct_0(B_435)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_695,plain,(
    ! [E_432] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_432,'#skF_3','#skF_6')
      | ~ r1_tarski(E_432,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_432,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_114,c_691])).

tff(c_702,plain,(
    ! [E_432] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_432,'#skF_3','#skF_6')
      | ~ r1_tarski(E_432,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_432,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_50,c_48,c_81,c_695])).

tff(c_704,plain,(
    ! [E_438] :
      ( ~ m1_connsp_2(E_438,'#skF_3','#skF_6')
      | ~ r1_tarski(E_438,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_438,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_54,c_103,c_702])).

tff(c_715,plain,(
    ! [B_43,C_47] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_43,C_47),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_43,C_47),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_47,'#skF_3',B_43)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_704])).

tff(c_737,plain,(
    ! [B_43,C_47] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_43,C_47),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_43,C_47),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_47,'#skF_3',B_43)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_715])).

tff(c_750,plain,(
    ! [B_441,C_442] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_441,C_442),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_441,C_442),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_442,'#skF_3',B_441)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_441,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_737])).

tff(c_758,plain,(
    ! [B_364] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_364,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_364)
      | ~ m1_subset_1(B_364,u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_305,c_750])).

tff(c_764,plain,(
    ! [B_364] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_364,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_364)
      | ~ m1_subset_1(B_364,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_758])).

tff(c_765,plain,(
    ! [B_364] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_364,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_364)
      | ~ m1_subset_1(B_364,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_764])).

tff(c_766,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_765])).

tff(c_772,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_766])).

tff(c_779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_772])).

tff(c_781,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_765])).

tff(c_206,plain,(
    ! [B_354,A_355,C_356] :
      ( m1_connsp_2(B_354,A_355,C_356)
      | ~ r2_hidden(C_356,B_354)
      | ~ v3_pre_topc(B_354,A_355)
      | ~ m1_subset_1(C_356,u1_struct_0(A_355))
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_214,plain,(
    ! [B_354] :
      ( m1_connsp_2(B_354,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_354)
      | ~ v3_pre_topc(B_354,'#skF_3')
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_206])).

tff(c_223,plain,(
    ! [B_354] :
      ( m1_connsp_2(B_354,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_354)
      | ~ v3_pre_topc(B_354,'#skF_3')
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_214])).

tff(c_224,plain,(
    ! [B_354] :
      ( m1_connsp_2(B_354,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_354)
      | ~ v3_pre_topc(B_354,'#skF_3')
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_223])).

tff(c_823,plain,
    ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_781,c_224])).

tff(c_827,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_830,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_199,c_827])).

tff(c_834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_52,c_830])).

tff(c_836,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_96,plain,(
    ! [B_310,A_311] :
      ( v2_pre_topc(B_310)
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_102,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_99])).

tff(c_88,plain,(
    ! [B_306,A_307] :
      ( l1_pre_topc(B_306)
      | ~ m1_pre_topc(B_306,A_307)
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_94,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_16,plain,(
    ! [B_27,A_25] :
      ( r2_hidden(B_27,k1_connsp_2(A_25,B_27))
      | ~ m1_subset_1(B_27,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_116,plain,(
    ! [A_322,B_323] :
      ( m1_subset_1(k1_connsp_2(A_322,B_323),k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ m1_subset_1(B_323,u1_struct_0(A_322))
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322)
      | v2_struct_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    ! [A_329,A_330,B_331] :
      ( ~ v1_xboole_0(u1_struct_0(A_329))
      | ~ r2_hidden(A_330,k1_connsp_2(A_329,B_331))
      | ~ m1_subset_1(B_331,u1_struct_0(A_329))
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(resolution,[status(thm)],[c_116,c_4])).

tff(c_149,plain,(
    ! [A_332,B_333] :
      ( ~ v1_xboole_0(u1_struct_0(A_332))
      | ~ m1_subset_1(B_333,u1_struct_0(A_332))
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(resolution,[status(thm)],[c_16,c_139])).

tff(c_158,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_81,c_149])).

tff(c_166,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_94,c_158])).

tff(c_167,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_166])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_835,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_855,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_859,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2,c_855])).

tff(c_862,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_859])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_862])).

tff(c_866,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_865,plain,(
    m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_241,plain,(
    ! [B_358] :
      ( m1_connsp_2(B_358,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_358)
      | ~ v3_pre_topc(B_358,'#skF_3')
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_223])).

tff(c_249,plain,(
    ! [B_58] :
      ( m1_connsp_2(u1_struct_0(B_58),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_58))
      | ~ v3_pre_topc(u1_struct_0(B_58),'#skF_3')
      | ~ m1_pre_topc(B_58,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_241])).

tff(c_264,plain,(
    ! [B_360] :
      ( m1_connsp_2(u1_struct_0(B_360),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_3')
      | ~ m1_pre_topc(B_360,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_249])).

tff(c_14,plain,(
    ! [C_24,A_21,B_22] :
      ( m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_connsp_2(C_24,A_21,B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_266,plain,(
    ! [B_360] :
      ( m1_subset_1(u1_struct_0(B_360),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_3')
      | ~ m1_pre_topc(B_360,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_264,c_14])).

tff(c_269,plain,(
    ! [B_360] :
      ( m1_subset_1(u1_struct_0(B_360),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_3')
      | ~ m1_pre_topc(B_360,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_266])).

tff(c_270,plain,(
    ! [B_360] :
      ( m1_subset_1(u1_struct_0(B_360),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_3')
      | ~ m1_pre_topc(B_360,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_269])).

tff(c_458,plain,(
    ! [A_382,B_383,C_384] :
      ( m1_connsp_2('#skF_1'(A_382,B_383,C_384),A_382,B_383)
      | ~ m1_connsp_2(C_384,A_382,B_383)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(u1_struct_0(A_382)))
      | ~ m1_subset_1(B_383,u1_struct_0(A_382))
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | v2_struct_0(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_464,plain,(
    ! [B_383,B_360] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_383,u1_struct_0(B_360)),'#skF_3',B_383)
      | ~ m1_connsp_2(u1_struct_0(B_360),'#skF_3',B_383)
      | ~ m1_subset_1(B_383,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_3')
      | ~ m1_pre_topc(B_360,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_270,c_458])).

tff(c_481,plain,(
    ! [B_383,B_360] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_383,u1_struct_0(B_360)),'#skF_3',B_383)
      | ~ m1_connsp_2(u1_struct_0(B_360),'#skF_3',B_383)
      | ~ m1_subset_1(B_383,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_3')
      | ~ m1_pre_topc(B_360,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_464])).

tff(c_482,plain,(
    ! [B_383,B_360] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_383,u1_struct_0(B_360)),'#skF_3',B_383)
      | ~ m1_connsp_2(u1_struct_0(B_360),'#skF_3',B_383)
      | ~ m1_subset_1(B_383,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_3')
      | ~ m1_pre_topc(B_360,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_481])).

tff(c_878,plain,(
    ! [B_451] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_451,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_451)
      | ~ m1_subset_1(B_451,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_765])).

tff(c_882,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_482,c_878])).

tff(c_890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_836,c_866,c_48,c_865,c_882])).

tff(c_892,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1326,plain,(
    ! [A_539,C_540,D_541,B_538,F_542] :
      ( r1_tmap_1(D_541,A_539,k2_tmap_1(B_538,A_539,C_540,D_541),F_542)
      | ~ r1_tmap_1(B_538,A_539,C_540,F_542)
      | ~ m1_subset_1(F_542,u1_struct_0(D_541))
      | ~ m1_subset_1(F_542,u1_struct_0(B_538))
      | ~ m1_pre_topc(D_541,B_538)
      | v2_struct_0(D_541)
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_538),u1_struct_0(A_539))))
      | ~ v1_funct_2(C_540,u1_struct_0(B_538),u1_struct_0(A_539))
      | ~ v1_funct_1(C_540)
      | ~ l1_pre_topc(B_538)
      | ~ v2_pre_topc(B_538)
      | v2_struct_0(B_538)
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_1328,plain,(
    ! [D_541,F_542] :
      ( r1_tmap_1(D_541,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_541),F_542)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_542)
      | ~ m1_subset_1(F_542,u1_struct_0(D_541))
      | ~ m1_subset_1(F_542,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_541,'#skF_3')
      | v2_struct_0(D_541)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_1326])).

tff(c_1331,plain,(
    ! [D_541,F_542] :
      ( r1_tmap_1(D_541,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_541),F_542)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_542)
      | ~ m1_subset_1(F_542,u1_struct_0(D_541))
      | ~ m1_subset_1(F_542,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_541,'#skF_3')
      | v2_struct_0(D_541)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_1328])).

tff(c_1333,plain,(
    ! [D_543,F_544] :
      ( r1_tmap_1(D_543,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_543),F_544)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_544)
      | ~ m1_subset_1(F_544,u1_struct_0(D_543))
      | ~ m1_subset_1(F_544,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_543,'#skF_3')
      | v2_struct_0(D_543) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1331])).

tff(c_891,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1336,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1333,c_891])).

tff(c_1339,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_81,c_892,c_1336])).

tff(c_1341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.25/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.76  
% 4.55/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.76  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.55/1.76  
% 4.55/1.76  %Foreground sorts:
% 4.55/1.76  
% 4.55/1.76  
% 4.55/1.76  %Background operators:
% 4.55/1.76  
% 4.55/1.76  
% 4.55/1.76  %Foreground operators:
% 4.55/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.55/1.76  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.55/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.55/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.55/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.76  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 4.55/1.76  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.55/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.55/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.55/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.76  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.55/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.55/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.55/1.76  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.55/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.55/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.55/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.76  
% 4.55/1.80  tff(f_310, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.55/1.80  tff(f_180, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.55/1.80  tff(f_173, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.55/1.80  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 4.55/1.80  tff(f_267, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 4.55/1.80  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.55/1.80  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.55/1.80  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.55/1.80  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 4.55/1.80  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 4.55/1.80  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.55/1.80  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.55/1.80  tff(f_95, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.55/1.80  tff(f_220, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.55/1.80  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_81, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 4.55/1.80  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_52, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_36, plain, (![B_58, A_56]: (m1_subset_1(u1_struct_0(B_58), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_pre_topc(B_58, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.55/1.80  tff(c_195, plain, (![B_347, A_348]: (v3_pre_topc(u1_struct_0(B_347), A_348) | ~v1_tsep_1(B_347, A_348) | ~m1_subset_1(u1_struct_0(B_347), k1_zfmisc_1(u1_struct_0(A_348))) | ~m1_pre_topc(B_347, A_348) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.80  tff(c_199, plain, (![B_58, A_56]: (v3_pre_topc(u1_struct_0(B_58), A_56) | ~v1_tsep_1(B_58, A_56) | ~v2_pre_topc(A_56) | ~m1_pre_topc(B_58, A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_36, c_195])).
% 4.55/1.80  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_287, plain, (![A_363, B_364, C_365]: (r1_tarski('#skF_1'(A_363, B_364, C_365), C_365) | ~m1_connsp_2(C_365, A_363, B_364) | ~m1_subset_1(C_365, k1_zfmisc_1(u1_struct_0(A_363))) | ~m1_subset_1(B_364, u1_struct_0(A_363)) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.55/1.80  tff(c_305, plain, (![A_56, B_364, B_58]: (r1_tarski('#skF_1'(A_56, B_364, u1_struct_0(B_58)), u1_struct_0(B_58)) | ~m1_connsp_2(u1_struct_0(B_58), A_56, B_364) | ~m1_subset_1(B_364, u1_struct_0(A_56)) | ~v2_pre_topc(A_56) | v2_struct_0(A_56) | ~m1_pre_topc(B_58, A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_36, c_287])).
% 4.55/1.80  tff(c_26, plain, (![A_35, B_43, C_47]: (m1_subset_1('#skF_1'(A_35, B_43, C_47), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_connsp_2(C_47, A_35, B_43) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_43, u1_struct_0(A_35)) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.55/1.80  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_74, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_83, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 4.55/1.80  tff(c_103, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_83])).
% 4.55/1.80  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.55/1.80  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 4.55/1.80  tff(c_114, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_103, c_82])).
% 4.55/1.80  tff(c_691, plain, (![E_432, B_435, G_433, C_437, D_434, A_436]: (r1_tmap_1(B_435, A_436, C_437, G_433) | ~r1_tmap_1(D_434, A_436, k2_tmap_1(B_435, A_436, C_437, D_434), G_433) | ~m1_connsp_2(E_432, B_435, G_433) | ~r1_tarski(E_432, u1_struct_0(D_434)) | ~m1_subset_1(G_433, u1_struct_0(D_434)) | ~m1_subset_1(G_433, u1_struct_0(B_435)) | ~m1_subset_1(E_432, k1_zfmisc_1(u1_struct_0(B_435))) | ~m1_pre_topc(D_434, B_435) | v2_struct_0(D_434) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_435), u1_struct_0(A_436)))) | ~v1_funct_2(C_437, u1_struct_0(B_435), u1_struct_0(A_436)) | ~v1_funct_1(C_437) | ~l1_pre_topc(B_435) | ~v2_pre_topc(B_435) | v2_struct_0(B_435) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_267])).
% 4.55/1.80  tff(c_695, plain, (![E_432]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_432, '#skF_3', '#skF_6') | ~r1_tarski(E_432, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_432, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_114, c_691])).
% 4.55/1.80  tff(c_702, plain, (![E_432]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_432, '#skF_3', '#skF_6') | ~r1_tarski(E_432, u1_struct_0('#skF_5')) | ~m1_subset_1(E_432, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_50, c_48, c_81, c_695])).
% 4.55/1.80  tff(c_704, plain, (![E_438]: (~m1_connsp_2(E_438, '#skF_3', '#skF_6') | ~r1_tarski(E_438, u1_struct_0('#skF_5')) | ~m1_subset_1(E_438, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_54, c_103, c_702])).
% 4.55/1.80  tff(c_715, plain, (![B_43, C_47]: (~m1_connsp_2('#skF_1'('#skF_3', B_43, C_47), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_43, C_47), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_47, '#skF_3', B_43) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_43, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_704])).
% 4.55/1.80  tff(c_737, plain, (![B_43, C_47]: (~m1_connsp_2('#skF_1'('#skF_3', B_43, C_47), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_43, C_47), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_47, '#skF_3', B_43) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_43, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_715])).
% 4.55/1.80  tff(c_750, plain, (![B_441, C_442]: (~m1_connsp_2('#skF_1'('#skF_3', B_441, C_442), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_441, C_442), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_442, '#skF_3', B_441) | ~m1_subset_1(C_442, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_441, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_737])).
% 4.55/1.80  tff(c_758, plain, (![B_364]: (~m1_connsp_2('#skF_1'('#skF_3', B_364, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_364) | ~m1_subset_1(B_364, u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_305, c_750])).
% 4.55/1.80  tff(c_764, plain, (![B_364]: (~m1_connsp_2('#skF_1'('#skF_3', B_364, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_364) | ~m1_subset_1(B_364, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_758])).
% 4.55/1.80  tff(c_765, plain, (![B_364]: (~m1_connsp_2('#skF_1'('#skF_3', B_364, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_364) | ~m1_subset_1(B_364, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_764])).
% 4.55/1.80  tff(c_766, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_765])).
% 4.55/1.80  tff(c_772, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_766])).
% 4.55/1.80  tff(c_779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_772])).
% 4.55/1.80  tff(c_781, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_765])).
% 4.55/1.80  tff(c_206, plain, (![B_354, A_355, C_356]: (m1_connsp_2(B_354, A_355, C_356) | ~r2_hidden(C_356, B_354) | ~v3_pre_topc(B_354, A_355) | ~m1_subset_1(C_356, u1_struct_0(A_355)) | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(A_355))) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355) | v2_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.55/1.80  tff(c_214, plain, (![B_354]: (m1_connsp_2(B_354, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_354) | ~v3_pre_topc(B_354, '#skF_3') | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_206])).
% 4.55/1.80  tff(c_223, plain, (![B_354]: (m1_connsp_2(B_354, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_354) | ~v3_pre_topc(B_354, '#skF_3') | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_214])).
% 4.55/1.80  tff(c_224, plain, (![B_354]: (m1_connsp_2(B_354, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_354) | ~v3_pre_topc(B_354, '#skF_3') | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_223])).
% 4.55/1.80  tff(c_823, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_781, c_224])).
% 4.55/1.80  tff(c_827, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_823])).
% 4.55/1.80  tff(c_830, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_199, c_827])).
% 4.55/1.80  tff(c_834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_52, c_830])).
% 4.55/1.80  tff(c_836, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_823])).
% 4.55/1.80  tff(c_96, plain, (![B_310, A_311]: (v2_pre_topc(B_310) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.80  tff(c_99, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_96])).
% 4.55/1.80  tff(c_102, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_99])).
% 4.55/1.80  tff(c_88, plain, (![B_306, A_307]: (l1_pre_topc(B_306) | ~m1_pre_topc(B_306, A_307) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.55/1.80  tff(c_91, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_88])).
% 4.55/1.80  tff(c_94, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 4.55/1.80  tff(c_16, plain, (![B_27, A_25]: (r2_hidden(B_27, k1_connsp_2(A_25, B_27)) | ~m1_subset_1(B_27, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.80  tff(c_116, plain, (![A_322, B_323]: (m1_subset_1(k1_connsp_2(A_322, B_323), k1_zfmisc_1(u1_struct_0(A_322))) | ~m1_subset_1(B_323, u1_struct_0(A_322)) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322) | v2_struct_0(A_322))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.55/1.80  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.55/1.80  tff(c_139, plain, (![A_329, A_330, B_331]: (~v1_xboole_0(u1_struct_0(A_329)) | ~r2_hidden(A_330, k1_connsp_2(A_329, B_331)) | ~m1_subset_1(B_331, u1_struct_0(A_329)) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329))), inference(resolution, [status(thm)], [c_116, c_4])).
% 4.55/1.80  tff(c_149, plain, (![A_332, B_333]: (~v1_xboole_0(u1_struct_0(A_332)) | ~m1_subset_1(B_333, u1_struct_0(A_332)) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(resolution, [status(thm)], [c_16, c_139])).
% 4.55/1.80  tff(c_158, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_81, c_149])).
% 4.55/1.80  tff(c_166, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_94, c_158])).
% 4.55/1.80  tff(c_167, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_166])).
% 4.55/1.80  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.80  tff(c_835, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_823])).
% 4.55/1.80  tff(c_855, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_835])).
% 4.55/1.80  tff(c_859, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_2, c_855])).
% 4.55/1.80  tff(c_862, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_859])).
% 4.55/1.80  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_862])).
% 4.55/1.80  tff(c_866, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_835])).
% 4.55/1.80  tff(c_865, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_835])).
% 4.55/1.80  tff(c_241, plain, (![B_358]: (m1_connsp_2(B_358, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_358) | ~v3_pre_topc(B_358, '#skF_3') | ~m1_subset_1(B_358, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_223])).
% 4.55/1.80  tff(c_249, plain, (![B_58]: (m1_connsp_2(u1_struct_0(B_58), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_58)) | ~v3_pre_topc(u1_struct_0(B_58), '#skF_3') | ~m1_pre_topc(B_58, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_241])).
% 4.55/1.80  tff(c_264, plain, (![B_360]: (m1_connsp_2(u1_struct_0(B_360), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_3') | ~m1_pre_topc(B_360, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_249])).
% 4.55/1.80  tff(c_14, plain, (![C_24, A_21, B_22]: (m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_connsp_2(C_24, A_21, B_22) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.55/1.80  tff(c_266, plain, (![B_360]: (m1_subset_1(u1_struct_0(B_360), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_3') | ~m1_pre_topc(B_360, '#skF_3'))), inference(resolution, [status(thm)], [c_264, c_14])).
% 4.55/1.80  tff(c_269, plain, (![B_360]: (m1_subset_1(u1_struct_0(B_360), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_3') | ~m1_pre_topc(B_360, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_266])).
% 4.55/1.80  tff(c_270, plain, (![B_360]: (m1_subset_1(u1_struct_0(B_360), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_3') | ~m1_pre_topc(B_360, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_269])).
% 4.55/1.80  tff(c_458, plain, (![A_382, B_383, C_384]: (m1_connsp_2('#skF_1'(A_382, B_383, C_384), A_382, B_383) | ~m1_connsp_2(C_384, A_382, B_383) | ~m1_subset_1(C_384, k1_zfmisc_1(u1_struct_0(A_382))) | ~m1_subset_1(B_383, u1_struct_0(A_382)) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | v2_struct_0(A_382))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.55/1.80  tff(c_464, plain, (![B_383, B_360]: (m1_connsp_2('#skF_1'('#skF_3', B_383, u1_struct_0(B_360)), '#skF_3', B_383) | ~m1_connsp_2(u1_struct_0(B_360), '#skF_3', B_383) | ~m1_subset_1(B_383, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_3') | ~m1_pre_topc(B_360, '#skF_3'))), inference(resolution, [status(thm)], [c_270, c_458])).
% 4.55/1.80  tff(c_481, plain, (![B_383, B_360]: (m1_connsp_2('#skF_1'('#skF_3', B_383, u1_struct_0(B_360)), '#skF_3', B_383) | ~m1_connsp_2(u1_struct_0(B_360), '#skF_3', B_383) | ~m1_subset_1(B_383, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_3') | ~m1_pre_topc(B_360, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_464])).
% 4.55/1.80  tff(c_482, plain, (![B_383, B_360]: (m1_connsp_2('#skF_1'('#skF_3', B_383, u1_struct_0(B_360)), '#skF_3', B_383) | ~m1_connsp_2(u1_struct_0(B_360), '#skF_3', B_383) | ~m1_subset_1(B_383, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_3') | ~m1_pre_topc(B_360, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_481])).
% 4.55/1.80  tff(c_878, plain, (![B_451]: (~m1_connsp_2('#skF_1'('#skF_3', B_451, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_451) | ~m1_subset_1(B_451, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_765])).
% 4.55/1.80  tff(c_882, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_482, c_878])).
% 4.55/1.80  tff(c_890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_836, c_866, c_48, c_865, c_882])).
% 4.55/1.80  tff(c_892, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 4.55/1.80  tff(c_1326, plain, (![A_539, C_540, D_541, B_538, F_542]: (r1_tmap_1(D_541, A_539, k2_tmap_1(B_538, A_539, C_540, D_541), F_542) | ~r1_tmap_1(B_538, A_539, C_540, F_542) | ~m1_subset_1(F_542, u1_struct_0(D_541)) | ~m1_subset_1(F_542, u1_struct_0(B_538)) | ~m1_pre_topc(D_541, B_538) | v2_struct_0(D_541) | ~m1_subset_1(C_540, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_538), u1_struct_0(A_539)))) | ~v1_funct_2(C_540, u1_struct_0(B_538), u1_struct_0(A_539)) | ~v1_funct_1(C_540) | ~l1_pre_topc(B_538) | ~v2_pre_topc(B_538) | v2_struct_0(B_538) | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(cnfTransformation, [status(thm)], [f_220])).
% 4.55/1.80  tff(c_1328, plain, (![D_541, F_542]: (r1_tmap_1(D_541, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_541), F_542) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_542) | ~m1_subset_1(F_542, u1_struct_0(D_541)) | ~m1_subset_1(F_542, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_541, '#skF_3') | v2_struct_0(D_541) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_1326])).
% 4.55/1.80  tff(c_1331, plain, (![D_541, F_542]: (r1_tmap_1(D_541, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_541), F_542) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_542) | ~m1_subset_1(F_542, u1_struct_0(D_541)) | ~m1_subset_1(F_542, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_541, '#skF_3') | v2_struct_0(D_541) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_1328])).
% 4.55/1.80  tff(c_1333, plain, (![D_543, F_544]: (r1_tmap_1(D_543, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_543), F_544) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_544) | ~m1_subset_1(F_544, u1_struct_0(D_543)) | ~m1_subset_1(F_544, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_543, '#skF_3') | v2_struct_0(D_543))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1331])).
% 4.55/1.80  tff(c_891, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 4.55/1.80  tff(c_1336, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1333, c_891])).
% 4.55/1.80  tff(c_1339, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_81, c_892, c_1336])).
% 4.55/1.80  tff(c_1341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1339])).
% 4.55/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  
% 4.55/1.80  Inference rules
% 4.55/1.80  ----------------------
% 4.55/1.80  #Ref     : 0
% 4.55/1.80  #Sup     : 220
% 4.55/1.80  #Fact    : 0
% 4.55/1.80  #Define  : 0
% 4.55/1.80  #Split   : 8
% 4.55/1.80  #Chain   : 0
% 4.55/1.80  #Close   : 0
% 4.55/1.80  
% 4.55/1.80  Ordering : KBO
% 4.55/1.80  
% 4.55/1.80  Simplification rules
% 4.55/1.80  ----------------------
% 4.55/1.80  #Subsume      : 54
% 4.55/1.80  #Demod        : 279
% 4.55/1.80  #Tautology    : 19
% 4.55/1.80  #SimpNegUnit  : 104
% 4.55/1.80  #BackRed      : 0
% 4.55/1.80  
% 4.55/1.80  #Partial instantiations: 0
% 4.55/1.80  #Strategies tried      : 1
% 4.55/1.80  
% 4.55/1.80  Timing (in seconds)
% 4.55/1.80  ----------------------
% 4.55/1.81  Preprocessing        : 0.40
% 4.55/1.81  Parsing              : 0.21
% 4.55/1.81  CNF conversion       : 0.05
% 4.55/1.81  Main loop            : 0.60
% 4.55/1.81  Inferencing          : 0.23
% 4.55/1.81  Reduction            : 0.18
% 4.55/1.81  Demodulation         : 0.12
% 4.55/1.81  BG Simplification    : 0.03
% 4.55/1.81  Subsumption          : 0.13
% 4.55/1.81  Abstraction          : 0.03
% 4.55/1.81  MUC search           : 0.00
% 4.55/1.81  Cooper               : 0.00
% 4.55/1.81  Total                : 1.08
% 4.55/1.81  Index Insertion      : 0.00
% 4.55/1.81  Index Deletion       : 0.00
% 4.55/1.81  Index Matching       : 0.00
% 4.55/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------

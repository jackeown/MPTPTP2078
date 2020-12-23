%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:41 EST 2020

% Result     : Theorem 10.55s
% Output     : CNFRefutation 10.55s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 121 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  297 ( 820 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(B,C)
                            & m1_pre_topc(D,E) )
                         => m1_pre_topc(k1_tsep_1(A,B,D),k1_tsep_1(A,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_pre_topc(k1_tsep_1(A_20,B_21,C_22),A_20)
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_24,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    ! [B_60,C_61,A_62] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0(C_61))
      | ~ m1_pre_topc(B_60,C_61)
      | ~ m1_pre_topc(C_61,A_62)
      | ~ m1_pre_topc(B_60,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_60,'#skF_3')
      | ~ m1_pre_topc(B_60,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_72,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_60,'#skF_3')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_58])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_60,'#skF_5')
      | ~ m1_pre_topc(B_60,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_62,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_60,'#skF_5')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_50])).

tff(c_10,plain,(
    ! [A_20,B_21,C_22] :
      ( v1_pre_topc(k1_tsep_1(A_20,B_21,C_22))
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_99,plain,(
    ! [A_83,B_84,C_85] :
      ( u1_struct_0(k1_tsep_1(A_83,B_84,C_85)) = k2_xboole_0(u1_struct_0(B_84),u1_struct_0(C_85))
      | ~ m1_pre_topc(k1_tsep_1(A_83,B_84,C_85),A_83)
      | ~ v1_pre_topc(k1_tsep_1(A_83,B_84,C_85))
      | v2_struct_0(k1_tsep_1(A_83,B_84,C_85))
      | ~ m1_pre_topc(C_85,A_83)
      | v2_struct_0(C_85)
      | ~ m1_pre_topc(B_84,A_83)
      | v2_struct_0(B_84)
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_107,plain,(
    ! [A_90,B_91,C_92] :
      ( u1_struct_0(k1_tsep_1(A_90,B_91,C_92)) = k2_xboole_0(u1_struct_0(B_91),u1_struct_0(C_92))
      | ~ v1_pre_topc(k1_tsep_1(A_90,B_91,C_92))
      | v2_struct_0(k1_tsep_1(A_90,B_91,C_92))
      | ~ m1_pre_topc(C_92,A_90)
      | v2_struct_0(C_92)
      | ~ m1_pre_topc(B_91,A_90)
      | v2_struct_0(B_91)
      | ~ l1_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_12,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ v2_struct_0(k1_tsep_1(A_20,B_21,C_22))
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_174,plain,(
    ! [A_93,B_94,C_95] :
      ( u1_struct_0(k1_tsep_1(A_93,B_94,C_95)) = k2_xboole_0(u1_struct_0(B_94),u1_struct_0(C_95))
      | ~ v1_pre_topc(k1_tsep_1(A_93,B_94,C_95))
      | ~ m1_pre_topc(C_95,A_93)
      | v2_struct_0(C_95)
      | ~ m1_pre_topc(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_107,c_12])).

tff(c_178,plain,(
    ! [A_96,B_97,C_98] :
      ( u1_struct_0(k1_tsep_1(A_96,B_97,C_98)) = k2_xboole_0(u1_struct_0(B_97),u1_struct_0(C_98))
      | ~ m1_pre_topc(C_98,A_96)
      | v2_struct_0(C_98)
      | ~ m1_pre_topc(B_97,A_96)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_10,c_174])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r1_tarski(k2_xboole_0(A_1,C_3),k2_xboole_0(B_2,D_4))
      | ~ r1_tarski(C_3,D_4)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_96,C_3,A_1,B_97,C_98] :
      ( r1_tarski(k2_xboole_0(A_1,C_3),u1_struct_0(k1_tsep_1(A_96,B_97,C_98)))
      | ~ r1_tarski(C_3,u1_struct_0(C_98))
      | ~ r1_tarski(A_1,u1_struct_0(B_97))
      | ~ m1_pre_topc(C_98,A_96)
      | v2_struct_0(C_98)
      | ~ m1_pre_topc(B_97,A_96)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_2])).

tff(c_16,plain,(
    ! [B_27,C_29,A_23] :
      ( m1_pre_topc(B_27,C_29)
      | ~ r1_tarski(u1_struct_0(B_27),u1_struct_0(C_29))
      | ~ m1_pre_topc(C_29,A_23)
      | ~ m1_pre_topc(B_27,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_439,plain,(
    ! [A_134,A_133,B_132,C_130,C_131] :
      ( m1_pre_topc(k1_tsep_1(A_133,B_132,C_130),C_131)
      | ~ r1_tarski(k2_xboole_0(u1_struct_0(B_132),u1_struct_0(C_130)),u1_struct_0(C_131))
      | ~ m1_pre_topc(C_131,A_134)
      | ~ m1_pre_topc(k1_tsep_1(A_133,B_132,C_130),A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | ~ m1_pre_topc(C_130,A_133)
      | v2_struct_0(C_130)
      | ~ m1_pre_topc(B_132,A_133)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_16])).

tff(c_1400,plain,(
    ! [C_375,C_381,A_380,A_379,A_378,B_377,B_376] :
      ( m1_pre_topc(k1_tsep_1(A_378,B_376,C_381),k1_tsep_1(A_379,B_377,C_375))
      | ~ m1_pre_topc(k1_tsep_1(A_379,B_377,C_375),A_380)
      | ~ m1_pre_topc(k1_tsep_1(A_378,B_376,C_381),A_380)
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | ~ m1_pre_topc(C_381,A_378)
      | v2_struct_0(C_381)
      | ~ m1_pre_topc(B_376,A_378)
      | v2_struct_0(B_376)
      | ~ l1_pre_topc(A_378)
      | v2_struct_0(A_378)
      | ~ r1_tarski(u1_struct_0(C_381),u1_struct_0(C_375))
      | ~ r1_tarski(u1_struct_0(B_376),u1_struct_0(B_377))
      | ~ m1_pre_topc(C_375,A_379)
      | v2_struct_0(C_375)
      | ~ m1_pre_topc(B_377,A_379)
      | v2_struct_0(B_377)
      | ~ l1_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(resolution,[status(thm)],[c_226,c_439])).

tff(c_1405,plain,(
    ! [B_393,A_390,C_389,A_392,B_391,C_388] :
      ( m1_pre_topc(k1_tsep_1(A_390,B_393,C_389),k1_tsep_1(A_392,B_391,C_388))
      | ~ m1_pre_topc(k1_tsep_1(A_390,B_393,C_389),A_392)
      | ~ v2_pre_topc(A_392)
      | ~ m1_pre_topc(C_389,A_390)
      | v2_struct_0(C_389)
      | ~ m1_pre_topc(B_393,A_390)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_390)
      | v2_struct_0(A_390)
      | ~ r1_tarski(u1_struct_0(C_389),u1_struct_0(C_388))
      | ~ r1_tarski(u1_struct_0(B_393),u1_struct_0(B_391))
      | ~ m1_pre_topc(C_388,A_392)
      | v2_struct_0(C_388)
      | ~ m1_pre_topc(B_391,A_392)
      | v2_struct_0(B_391)
      | ~ l1_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_8,c_1400])).

tff(c_1439,plain,(
    ! [B_393,A_390,A_392,B_391,B_60] :
      ( m1_pre_topc(k1_tsep_1(A_390,B_393,B_60),k1_tsep_1(A_392,B_391,'#skF_5'))
      | ~ m1_pre_topc(k1_tsep_1(A_390,B_393,B_60),A_392)
      | ~ v2_pre_topc(A_392)
      | ~ m1_pre_topc(B_60,A_390)
      | v2_struct_0(B_60)
      | ~ m1_pre_topc(B_393,A_390)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_390)
      | v2_struct_0(A_390)
      | ~ r1_tarski(u1_struct_0(B_393),u1_struct_0(B_391))
      | ~ m1_pre_topc('#skF_5',A_392)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_391,A_392)
      | v2_struct_0(B_391)
      | ~ l1_pre_topc(A_392)
      | v2_struct_0(A_392)
      | ~ m1_pre_topc(B_60,'#skF_5')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_1405])).

tff(c_3704,plain,(
    ! [B_601,A_599,B_600,A_602,B_603] :
      ( m1_pre_topc(k1_tsep_1(A_602,B_603,B_601),k1_tsep_1(A_599,B_600,'#skF_5'))
      | ~ m1_pre_topc(k1_tsep_1(A_602,B_603,B_601),A_599)
      | ~ v2_pre_topc(A_599)
      | ~ m1_pre_topc(B_601,A_602)
      | v2_struct_0(B_601)
      | ~ m1_pre_topc(B_603,A_602)
      | v2_struct_0(B_603)
      | ~ l1_pre_topc(A_602)
      | v2_struct_0(A_602)
      | ~ r1_tarski(u1_struct_0(B_603),u1_struct_0(B_600))
      | ~ m1_pre_topc('#skF_5',A_599)
      | ~ m1_pre_topc(B_600,A_599)
      | v2_struct_0(B_600)
      | ~ l1_pre_topc(A_599)
      | v2_struct_0(A_599)
      | ~ m1_pre_topc(B_601,'#skF_5')
      | ~ m1_pre_topc(B_601,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1439])).

tff(c_3744,plain,(
    ! [A_602,B_60,B_601,A_599] :
      ( m1_pre_topc(k1_tsep_1(A_602,B_60,B_601),k1_tsep_1(A_599,'#skF_3','#skF_5'))
      | ~ m1_pre_topc(k1_tsep_1(A_602,B_60,B_601),A_599)
      | ~ v2_pre_topc(A_599)
      | ~ m1_pre_topc(B_601,A_602)
      | v2_struct_0(B_601)
      | ~ m1_pre_topc(B_60,A_602)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_602)
      | v2_struct_0(A_602)
      | ~ m1_pre_topc('#skF_5',A_599)
      | ~ m1_pre_topc('#skF_3',A_599)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_599)
      | v2_struct_0(A_599)
      | ~ m1_pre_topc(B_601,'#skF_5')
      | ~ m1_pre_topc(B_601,'#skF_1')
      | ~ m1_pre_topc(B_60,'#skF_3')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_72,c_3704])).

tff(c_4319,plain,(
    ! [A_645,B_646,B_647,A_648] :
      ( m1_pre_topc(k1_tsep_1(A_645,B_646,B_647),k1_tsep_1(A_648,'#skF_3','#skF_5'))
      | ~ m1_pre_topc(k1_tsep_1(A_645,B_646,B_647),A_648)
      | ~ v2_pre_topc(A_648)
      | ~ m1_pre_topc(B_647,A_645)
      | v2_struct_0(B_647)
      | ~ m1_pre_topc(B_646,A_645)
      | v2_struct_0(B_646)
      | ~ l1_pre_topc(A_645)
      | v2_struct_0(A_645)
      | ~ m1_pre_topc('#skF_5',A_648)
      | ~ m1_pre_topc('#skF_3',A_648)
      | ~ l1_pre_topc(A_648)
      | v2_struct_0(A_648)
      | ~ m1_pre_topc(B_647,'#skF_5')
      | ~ m1_pre_topc(B_647,'#skF_1')
      | ~ m1_pre_topc(B_646,'#skF_3')
      | ~ m1_pre_topc(B_646,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3744])).

tff(c_18,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),k1_tsep_1('#skF_1','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4368,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_4319,c_18])).

tff(c_4400,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22,c_28,c_20,c_40,c_32,c_24,c_42,c_4368])).

tff(c_4401,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_30,c_4400])).

tff(c_4404,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_4401])).

tff(c_4407,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_28,c_4404])).

tff(c_4409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_30,c_4407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n020.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 15:37:22 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.55/3.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.55/3.56  
% 10.55/3.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.55/3.57  %$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.55/3.57  
% 10.55/3.57  %Foreground sorts:
% 10.55/3.57  
% 10.55/3.57  
% 10.55/3.57  %Background operators:
% 10.55/3.57  
% 10.55/3.57  
% 10.55/3.57  %Foreground operators:
% 10.55/3.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.55/3.57  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 10.55/3.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.55/3.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.55/3.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.55/3.57  tff('#skF_5', type, '#skF_5': $i).
% 10.55/3.57  tff('#skF_2', type, '#skF_2': $i).
% 10.55/3.57  tff('#skF_3', type, '#skF_3': $i).
% 10.55/3.57  tff('#skF_1', type, '#skF_1': $i).
% 10.55/3.57  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.55/3.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.55/3.57  tff('#skF_4', type, '#skF_4': $i).
% 10.55/3.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.55/3.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.55/3.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.55/3.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.55/3.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.55/3.57  
% 10.55/3.58  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, E)) => m1_pre_topc(k1_tsep_1(A, B, D), k1_tsep_1(A, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tmap_1)).
% 10.55/3.58  tff(f_82, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 10.55/3.58  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 10.55/3.58  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 10.55/3.58  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 10.55/3.58  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_30, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_8, plain, (![A_20, B_21, C_22]: (m1_pre_topc(k1_tsep_1(A_20, B_21, C_22), A_20) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.55/3.58  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_20, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_24, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_46, plain, (![B_60, C_61, A_62]: (r1_tarski(u1_struct_0(B_60), u1_struct_0(C_61)) | ~m1_pre_topc(B_60, C_61) | ~m1_pre_topc(C_61, A_62) | ~m1_pre_topc(B_60, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.55/3.58  tff(c_58, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_60, '#skF_3') | ~m1_pre_topc(B_60, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_46])).
% 10.55/3.58  tff(c_72, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_60, '#skF_3') | ~m1_pre_topc(B_60, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_58])).
% 10.55/3.58  tff(c_26, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_50, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_60, '#skF_5') | ~m1_pre_topc(B_60, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_46])).
% 10.55/3.58  tff(c_62, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_60, '#skF_5') | ~m1_pre_topc(B_60, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_50])).
% 10.55/3.58  tff(c_10, plain, (![A_20, B_21, C_22]: (v1_pre_topc(k1_tsep_1(A_20, B_21, C_22)) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.55/3.58  tff(c_99, plain, (![A_83, B_84, C_85]: (u1_struct_0(k1_tsep_1(A_83, B_84, C_85))=k2_xboole_0(u1_struct_0(B_84), u1_struct_0(C_85)) | ~m1_pre_topc(k1_tsep_1(A_83, B_84, C_85), A_83) | ~v1_pre_topc(k1_tsep_1(A_83, B_84, C_85)) | v2_struct_0(k1_tsep_1(A_83, B_84, C_85)) | ~m1_pre_topc(C_85, A_83) | v2_struct_0(C_85) | ~m1_pre_topc(B_84, A_83) | v2_struct_0(B_84) | ~l1_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.55/3.58  tff(c_107, plain, (![A_90, B_91, C_92]: (u1_struct_0(k1_tsep_1(A_90, B_91, C_92))=k2_xboole_0(u1_struct_0(B_91), u1_struct_0(C_92)) | ~v1_pre_topc(k1_tsep_1(A_90, B_91, C_92)) | v2_struct_0(k1_tsep_1(A_90, B_91, C_92)) | ~m1_pre_topc(C_92, A_90) | v2_struct_0(C_92) | ~m1_pre_topc(B_91, A_90) | v2_struct_0(B_91) | ~l1_pre_topc(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_8, c_99])).
% 10.55/3.58  tff(c_12, plain, (![A_20, B_21, C_22]: (~v2_struct_0(k1_tsep_1(A_20, B_21, C_22)) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.55/3.58  tff(c_174, plain, (![A_93, B_94, C_95]: (u1_struct_0(k1_tsep_1(A_93, B_94, C_95))=k2_xboole_0(u1_struct_0(B_94), u1_struct_0(C_95)) | ~v1_pre_topc(k1_tsep_1(A_93, B_94, C_95)) | ~m1_pre_topc(C_95, A_93) | v2_struct_0(C_95) | ~m1_pre_topc(B_94, A_93) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_107, c_12])).
% 10.55/3.58  tff(c_178, plain, (![A_96, B_97, C_98]: (u1_struct_0(k1_tsep_1(A_96, B_97, C_98))=k2_xboole_0(u1_struct_0(B_97), u1_struct_0(C_98)) | ~m1_pre_topc(C_98, A_96) | v2_struct_0(C_98) | ~m1_pre_topc(B_97, A_96) | v2_struct_0(B_97) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_10, c_174])).
% 10.55/3.58  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (r1_tarski(k2_xboole_0(A_1, C_3), k2_xboole_0(B_2, D_4)) | ~r1_tarski(C_3, D_4) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.55/3.58  tff(c_226, plain, (![A_96, C_3, A_1, B_97, C_98]: (r1_tarski(k2_xboole_0(A_1, C_3), u1_struct_0(k1_tsep_1(A_96, B_97, C_98))) | ~r1_tarski(C_3, u1_struct_0(C_98)) | ~r1_tarski(A_1, u1_struct_0(B_97)) | ~m1_pre_topc(C_98, A_96) | v2_struct_0(C_98) | ~m1_pre_topc(B_97, A_96) | v2_struct_0(B_97) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(superposition, [status(thm), theory('equality')], [c_178, c_2])).
% 10.55/3.58  tff(c_16, plain, (![B_27, C_29, A_23]: (m1_pre_topc(B_27, C_29) | ~r1_tarski(u1_struct_0(B_27), u1_struct_0(C_29)) | ~m1_pre_topc(C_29, A_23) | ~m1_pre_topc(B_27, A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.55/3.58  tff(c_439, plain, (![A_134, A_133, B_132, C_130, C_131]: (m1_pre_topc(k1_tsep_1(A_133, B_132, C_130), C_131) | ~r1_tarski(k2_xboole_0(u1_struct_0(B_132), u1_struct_0(C_130)), u1_struct_0(C_131)) | ~m1_pre_topc(C_131, A_134) | ~m1_pre_topc(k1_tsep_1(A_133, B_132, C_130), A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | ~m1_pre_topc(C_130, A_133) | v2_struct_0(C_130) | ~m1_pre_topc(B_132, A_133) | v2_struct_0(B_132) | ~l1_pre_topc(A_133) | v2_struct_0(A_133))), inference(superposition, [status(thm), theory('equality')], [c_178, c_16])).
% 10.55/3.58  tff(c_1400, plain, (![C_375, C_381, A_380, A_379, A_378, B_377, B_376]: (m1_pre_topc(k1_tsep_1(A_378, B_376, C_381), k1_tsep_1(A_379, B_377, C_375)) | ~m1_pre_topc(k1_tsep_1(A_379, B_377, C_375), A_380) | ~m1_pre_topc(k1_tsep_1(A_378, B_376, C_381), A_380) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | ~m1_pre_topc(C_381, A_378) | v2_struct_0(C_381) | ~m1_pre_topc(B_376, A_378) | v2_struct_0(B_376) | ~l1_pre_topc(A_378) | v2_struct_0(A_378) | ~r1_tarski(u1_struct_0(C_381), u1_struct_0(C_375)) | ~r1_tarski(u1_struct_0(B_376), u1_struct_0(B_377)) | ~m1_pre_topc(C_375, A_379) | v2_struct_0(C_375) | ~m1_pre_topc(B_377, A_379) | v2_struct_0(B_377) | ~l1_pre_topc(A_379) | v2_struct_0(A_379))), inference(resolution, [status(thm)], [c_226, c_439])).
% 10.55/3.58  tff(c_1405, plain, (![B_393, A_390, C_389, A_392, B_391, C_388]: (m1_pre_topc(k1_tsep_1(A_390, B_393, C_389), k1_tsep_1(A_392, B_391, C_388)) | ~m1_pre_topc(k1_tsep_1(A_390, B_393, C_389), A_392) | ~v2_pre_topc(A_392) | ~m1_pre_topc(C_389, A_390) | v2_struct_0(C_389) | ~m1_pre_topc(B_393, A_390) | v2_struct_0(B_393) | ~l1_pre_topc(A_390) | v2_struct_0(A_390) | ~r1_tarski(u1_struct_0(C_389), u1_struct_0(C_388)) | ~r1_tarski(u1_struct_0(B_393), u1_struct_0(B_391)) | ~m1_pre_topc(C_388, A_392) | v2_struct_0(C_388) | ~m1_pre_topc(B_391, A_392) | v2_struct_0(B_391) | ~l1_pre_topc(A_392) | v2_struct_0(A_392))), inference(resolution, [status(thm)], [c_8, c_1400])).
% 10.55/3.58  tff(c_1439, plain, (![B_393, A_390, A_392, B_391, B_60]: (m1_pre_topc(k1_tsep_1(A_390, B_393, B_60), k1_tsep_1(A_392, B_391, '#skF_5')) | ~m1_pre_topc(k1_tsep_1(A_390, B_393, B_60), A_392) | ~v2_pre_topc(A_392) | ~m1_pre_topc(B_60, A_390) | v2_struct_0(B_60) | ~m1_pre_topc(B_393, A_390) | v2_struct_0(B_393) | ~l1_pre_topc(A_390) | v2_struct_0(A_390) | ~r1_tarski(u1_struct_0(B_393), u1_struct_0(B_391)) | ~m1_pre_topc('#skF_5', A_392) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_391, A_392) | v2_struct_0(B_391) | ~l1_pre_topc(A_392) | v2_struct_0(A_392) | ~m1_pre_topc(B_60, '#skF_5') | ~m1_pre_topc(B_60, '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_1405])).
% 10.55/3.58  tff(c_3704, plain, (![B_601, A_599, B_600, A_602, B_603]: (m1_pre_topc(k1_tsep_1(A_602, B_603, B_601), k1_tsep_1(A_599, B_600, '#skF_5')) | ~m1_pre_topc(k1_tsep_1(A_602, B_603, B_601), A_599) | ~v2_pre_topc(A_599) | ~m1_pre_topc(B_601, A_602) | v2_struct_0(B_601) | ~m1_pre_topc(B_603, A_602) | v2_struct_0(B_603) | ~l1_pre_topc(A_602) | v2_struct_0(A_602) | ~r1_tarski(u1_struct_0(B_603), u1_struct_0(B_600)) | ~m1_pre_topc('#skF_5', A_599) | ~m1_pre_topc(B_600, A_599) | v2_struct_0(B_600) | ~l1_pre_topc(A_599) | v2_struct_0(A_599) | ~m1_pre_topc(B_601, '#skF_5') | ~m1_pre_topc(B_601, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_26, c_1439])).
% 10.55/3.58  tff(c_3744, plain, (![A_602, B_60, B_601, A_599]: (m1_pre_topc(k1_tsep_1(A_602, B_60, B_601), k1_tsep_1(A_599, '#skF_3', '#skF_5')) | ~m1_pre_topc(k1_tsep_1(A_602, B_60, B_601), A_599) | ~v2_pre_topc(A_599) | ~m1_pre_topc(B_601, A_602) | v2_struct_0(B_601) | ~m1_pre_topc(B_60, A_602) | v2_struct_0(B_60) | ~l1_pre_topc(A_602) | v2_struct_0(A_602) | ~m1_pre_topc('#skF_5', A_599) | ~m1_pre_topc('#skF_3', A_599) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_599) | v2_struct_0(A_599) | ~m1_pre_topc(B_601, '#skF_5') | ~m1_pre_topc(B_601, '#skF_1') | ~m1_pre_topc(B_60, '#skF_3') | ~m1_pre_topc(B_60, '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_3704])).
% 10.55/3.58  tff(c_4319, plain, (![A_645, B_646, B_647, A_648]: (m1_pre_topc(k1_tsep_1(A_645, B_646, B_647), k1_tsep_1(A_648, '#skF_3', '#skF_5')) | ~m1_pre_topc(k1_tsep_1(A_645, B_646, B_647), A_648) | ~v2_pre_topc(A_648) | ~m1_pre_topc(B_647, A_645) | v2_struct_0(B_647) | ~m1_pre_topc(B_646, A_645) | v2_struct_0(B_646) | ~l1_pre_topc(A_645) | v2_struct_0(A_645) | ~m1_pre_topc('#skF_5', A_648) | ~m1_pre_topc('#skF_3', A_648) | ~l1_pre_topc(A_648) | v2_struct_0(A_648) | ~m1_pre_topc(B_647, '#skF_5') | ~m1_pre_topc(B_647, '#skF_1') | ~m1_pre_topc(B_646, '#skF_3') | ~m1_pre_topc(B_646, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_34, c_3744])).
% 10.55/3.58  tff(c_18, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), k1_tsep_1('#skF_1', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.55/3.58  tff(c_4368, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_4319, c_18])).
% 10.55/3.58  tff(c_4400, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22, c_28, c_20, c_40, c_32, c_24, c_42, c_4368])).
% 10.55/3.58  tff(c_4401, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_30, c_4400])).
% 10.55/3.58  tff(c_4404, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_4401])).
% 10.55/3.58  tff(c_4407, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_28, c_4404])).
% 10.55/3.58  tff(c_4409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_30, c_4407])).
% 10.55/3.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.55/3.58  
% 10.55/3.58  Inference rules
% 10.55/3.58  ----------------------
% 10.55/3.58  #Ref     : 2
% 10.55/3.58  #Sup     : 1308
% 10.55/3.58  #Fact    : 0
% 10.55/3.58  #Define  : 0
% 10.55/3.58  #Split   : 5
% 10.55/3.58  #Chain   : 0
% 10.55/3.58  #Close   : 0
% 10.55/3.58  
% 10.55/3.58  Ordering : KBO
% 10.55/3.58  
% 10.55/3.58  Simplification rules
% 10.55/3.58  ----------------------
% 10.55/3.58  #Subsume      : 300
% 10.55/3.58  #Demod        : 40
% 10.55/3.58  #Tautology    : 14
% 10.55/3.58  #SimpNegUnit  : 203
% 10.55/3.58  #BackRed      : 0
% 10.55/3.58  
% 10.55/3.58  #Partial instantiations: 0
% 10.55/3.58  #Strategies tried      : 1
% 10.55/3.58  
% 10.55/3.58  Timing (in seconds)
% 10.55/3.58  ----------------------
% 10.55/3.58  Preprocessing        : 0.31
% 10.55/3.58  Parsing              : 0.17
% 10.55/3.58  CNF conversion       : 0.03
% 10.55/3.58  Main loop            : 2.57
% 10.55/3.59  Inferencing          : 0.70
% 10.55/3.59  Reduction            : 0.45
% 10.55/3.59  Demodulation         : 0.29
% 10.55/3.59  BG Simplification    : 0.08
% 10.55/3.59  Subsumption          : 1.22
% 10.55/3.59  Abstraction          : 0.11
% 10.55/3.59  MUC search           : 0.00
% 10.55/3.59  Cooper               : 0.00
% 10.55/3.59  Total                : 2.92
% 10.55/3.59  Index Insertion      : 0.00
% 10.55/3.59  Index Deletion       : 0.00
% 10.55/3.59  Index Matching       : 0.00
% 10.55/3.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

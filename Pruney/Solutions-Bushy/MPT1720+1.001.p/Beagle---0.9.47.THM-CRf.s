%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1720+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:18 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 101 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  224 ( 573 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_127,negated_conjecture,(
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
                   => ( ( m1_pre_topc(B,C)
                        & m1_pre_topc(D,C) )
                     => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_53,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_pre_topc(k1_tsep_1(A_16,B_17,C_18),A_16)
      | ~ m1_pre_topc(C_18,A_16)
      | v2_struct_0(C_18)
      | ~ m1_pre_topc(B_17,A_16)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_20,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    ! [B_43,C_44,A_45] :
      ( r1_tarski(u1_struct_0(B_43),u1_struct_0(C_44))
      | ~ m1_pre_topc(B_43,C_44)
      | ~ m1_pre_topc(C_44,A_45)
      | ~ m1_pre_topc(B_43,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    ! [B_43] :
      ( r1_tarski(u1_struct_0(B_43),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_43,'#skF_3')
      | ~ m1_pre_topc(B_43,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_42])).

tff(c_63,plain,(
    ! [B_43] :
      ( r1_tarski(u1_struct_0(B_43),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_43,'#skF_3')
      | ~ m1_pre_topc(B_43,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_52])).

tff(c_16,plain,(
    ! [A_26,C_28,B_27] :
      ( r1_tarski(k2_xboole_0(A_26,C_28),B_27)
      | ~ r1_tarski(C_28,B_27)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8,plain,(
    ! [A_16,B_17,C_18] :
      ( v1_pre_topc(k1_tsep_1(A_16,B_17,C_18))
      | ~ m1_pre_topc(C_18,A_16)
      | v2_struct_0(C_18)
      | ~ m1_pre_topc(B_17,A_16)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_90,plain,(
    ! [A_69,B_70,C_71] :
      ( u1_struct_0(k1_tsep_1(A_69,B_70,C_71)) = k2_xboole_0(u1_struct_0(B_70),u1_struct_0(C_71))
      | ~ m1_pre_topc(k1_tsep_1(A_69,B_70,C_71),A_69)
      | ~ v1_pre_topc(k1_tsep_1(A_69,B_70,C_71))
      | v2_struct_0(k1_tsep_1(A_69,B_70,C_71))
      | ~ m1_pre_topc(C_71,A_69)
      | v2_struct_0(C_71)
      | ~ m1_pre_topc(B_70,A_69)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,(
    ! [A_72,B_73,C_74] :
      ( u1_struct_0(k1_tsep_1(A_72,B_73,C_74)) = k2_xboole_0(u1_struct_0(B_73),u1_struct_0(C_74))
      | ~ v1_pre_topc(k1_tsep_1(A_72,B_73,C_74))
      | v2_struct_0(k1_tsep_1(A_72,B_73,C_74))
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18] :
      ( ~ v2_struct_0(k1_tsep_1(A_16,B_17,C_18))
      | ~ m1_pre_topc(C_18,A_16)
      | v2_struct_0(C_18)
      | ~ m1_pre_topc(B_17,A_16)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_162,plain,(
    ! [A_78,B_79,C_80] :
      ( u1_struct_0(k1_tsep_1(A_78,B_79,C_80)) = k2_xboole_0(u1_struct_0(B_79),u1_struct_0(C_80))
      | ~ v1_pre_topc(k1_tsep_1(A_78,B_79,C_80))
      | ~ m1_pre_topc(C_80,A_78)
      | v2_struct_0(C_80)
      | ~ m1_pre_topc(B_79,A_78)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_94,c_10])).

tff(c_166,plain,(
    ! [A_81,B_82,C_83] :
      ( u1_struct_0(k1_tsep_1(A_81,B_82,C_83)) = k2_xboole_0(u1_struct_0(B_82),u1_struct_0(C_83))
      | ~ m1_pre_topc(C_83,A_81)
      | v2_struct_0(C_83)
      | ~ m1_pre_topc(B_82,A_81)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_14,plain,(
    ! [B_23,C_25,A_19] :
      ( m1_pre_topc(B_23,C_25)
      | ~ r1_tarski(u1_struct_0(B_23),u1_struct_0(C_25))
      | ~ m1_pre_topc(C_25,A_19)
      | ~ m1_pre_topc(B_23,A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_394,plain,(
    ! [A_108,B_110,C_109,A_107,C_106] :
      ( m1_pre_topc(k1_tsep_1(A_107,B_110,C_109),C_106)
      | ~ r1_tarski(k2_xboole_0(u1_struct_0(B_110),u1_struct_0(C_109)),u1_struct_0(C_106))
      | ~ m1_pre_topc(C_106,A_108)
      | ~ m1_pre_topc(k1_tsep_1(A_107,B_110,C_109),A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | ~ m1_pre_topc(C_109,A_107)
      | v2_struct_0(C_109)
      | ~ m1_pre_topc(B_110,A_107)
      | v2_struct_0(B_110)
      | ~ l1_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_14])).

tff(c_447,plain,(
    ! [B_118,A_119,A_117,C_120,C_116] :
      ( m1_pre_topc(k1_tsep_1(A_119,B_118,C_116),C_120)
      | ~ m1_pre_topc(C_120,A_117)
      | ~ m1_pre_topc(k1_tsep_1(A_119,B_118,C_116),A_117)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | ~ m1_pre_topc(C_116,A_119)
      | v2_struct_0(C_116)
      | ~ m1_pre_topc(B_118,A_119)
      | v2_struct_0(B_118)
      | ~ l1_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ r1_tarski(u1_struct_0(C_116),u1_struct_0(C_120))
      | ~ r1_tarski(u1_struct_0(B_118),u1_struct_0(C_120)) ) ),
    inference(resolution,[status(thm)],[c_16,c_394])).

tff(c_459,plain,(
    ! [A_119,B_118,C_116] :
      ( m1_pre_topc(k1_tsep_1(A_119,B_118,C_116),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_119,B_118,C_116),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_116,A_119)
      | v2_struct_0(C_116)
      | ~ m1_pre_topc(B_118,A_119)
      | v2_struct_0(B_118)
      | ~ l1_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ r1_tarski(u1_struct_0(C_116),u1_struct_0('#skF_3'))
      | ~ r1_tarski(u1_struct_0(B_118),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_28,c_447])).

tff(c_521,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_pre_topc(k1_tsep_1(A_130,B_131,C_132),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_130,B_131,C_132),'#skF_1')
      | ~ m1_pre_topc(C_132,A_130)
      | v2_struct_0(C_132)
      | ~ m1_pre_topc(B_131,A_130)
      | v2_struct_0(B_131)
      | ~ l1_pre_topc(A_130)
      | v2_struct_0(A_130)
      | ~ r1_tarski(u1_struct_0(C_132),u1_struct_0('#skF_3'))
      | ~ r1_tarski(u1_struct_0(B_131),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_459])).

tff(c_549,plain,(
    ! [A_136,B_137,B_138] :
      ( m1_pre_topc(k1_tsep_1(A_136,B_137,B_138),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_136,B_137,B_138),'#skF_1')
      | ~ m1_pre_topc(B_138,A_136)
      | v2_struct_0(B_138)
      | ~ m1_pre_topc(B_137,A_136)
      | v2_struct_0(B_137)
      | ~ l1_pre_topc(A_136)
      | v2_struct_0(A_136)
      | ~ r1_tarski(u1_struct_0(B_137),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_138,'#skF_3')
      | ~ m1_pre_topc(B_138,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_63,c_521])).

tff(c_609,plain,(
    ! [A_152,B_153,B_154] :
      ( m1_pre_topc(k1_tsep_1(A_152,B_153,B_154),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_152,B_153,B_154),'#skF_1')
      | ~ m1_pre_topc(B_154,A_152)
      | v2_struct_0(B_154)
      | ~ m1_pre_topc(B_153,A_152)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_152)
      | v2_struct_0(A_152)
      | ~ m1_pre_topc(B_154,'#skF_3')
      | ~ m1_pre_topc(B_154,'#skF_1')
      | ~ m1_pre_topc(B_153,'#skF_3')
      | ~ m1_pre_topc(B_153,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_63,c_549])).

tff(c_18,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_620,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_609,c_18])).

tff(c_629,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22,c_24,c_20,c_36,c_620])).

tff(c_630,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_26,c_629])).

tff(c_633,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_630])).

tff(c_636,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_24,c_633])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_26,c_636])).

%------------------------------------------------------------------------------

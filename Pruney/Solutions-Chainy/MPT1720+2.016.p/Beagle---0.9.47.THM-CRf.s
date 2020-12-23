%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:43 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 101 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 ( 570 expanded)
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

tff(f_128,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_pre_topc(k1_tsep_1(A_19,B_20,C_21),A_19)
      | ~ m1_pre_topc(C_21,A_19)
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,A_19)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_20,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_43,plain,(
    ! [B_46,C_47,A_48] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0(C_47))
      | ~ m1_pre_topc(B_46,C_47)
      | ~ m1_pre_topc(C_47,A_48)
      | ~ m1_pre_topc(B_46,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_53,plain,(
    ! [B_46] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_46,'#skF_3')
      | ~ m1_pre_topc(B_46,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_64,plain,(
    ! [B_46] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_46,'#skF_3')
      | ~ m1_pre_topc(B_46,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_53])).

tff(c_10,plain,(
    ! [A_19,B_20,C_21] :
      ( v1_pre_topc(k1_tsep_1(A_19,B_20,C_21))
      | ~ m1_pre_topc(C_21,A_19)
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,A_19)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_85,plain,(
    ! [A_65,B_66,C_67] :
      ( u1_struct_0(k1_tsep_1(A_65,B_66,C_67)) = k2_xboole_0(u1_struct_0(B_66),u1_struct_0(C_67))
      | ~ m1_pre_topc(k1_tsep_1(A_65,B_66,C_67),A_65)
      | ~ v1_pre_topc(k1_tsep_1(A_65,B_66,C_67))
      | v2_struct_0(k1_tsep_1(A_65,B_66,C_67))
      | ~ m1_pre_topc(C_67,A_65)
      | v2_struct_0(C_67)
      | ~ m1_pre_topc(B_66,A_65)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
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
    inference(resolution,[status(thm)],[c_8,c_85])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ v2_struct_0(k1_tsep_1(A_19,B_20,C_21))
      | ~ m1_pre_topc(C_21,A_19)
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,A_19)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    ! [A_75,B_76,C_77] :
      ( u1_struct_0(k1_tsep_1(A_75,B_76,C_77)) = k2_xboole_0(u1_struct_0(B_76),u1_struct_0(C_77))
      | ~ v1_pre_topc(k1_tsep_1(A_75,B_76,C_77))
      | ~ m1_pre_topc(C_77,A_75)
      | v2_struct_0(C_77)
      | ~ m1_pre_topc(B_76,A_75)
      | v2_struct_0(B_76)
      | ~ l1_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_165,plain,(
    ! [A_81,B_82,C_83] :
      ( u1_struct_0(k1_tsep_1(A_81,B_82,C_83)) = k2_xboole_0(u1_struct_0(B_82),u1_struct_0(C_83))
      | ~ m1_pre_topc(C_83,A_81)
      | v2_struct_0(C_83)
      | ~ m1_pre_topc(B_82,A_81)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k2_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(C_3,B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ! [A_84,B_85,C_86,B_87] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(A_84,B_85,C_86)),B_87)
      | ~ r1_tarski(u1_struct_0(C_86),B_87)
      | ~ r1_tarski(u1_struct_0(B_85),B_87)
      | ~ m1_pre_topc(C_86,A_84)
      | v2_struct_0(C_86)
      | ~ m1_pre_topc(B_85,A_84)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_2])).

tff(c_16,plain,(
    ! [B_26,C_28,A_22] :
      ( m1_pre_topc(B_26,C_28)
      | ~ r1_tarski(u1_struct_0(B_26),u1_struct_0(C_28))
      | ~ m1_pre_topc(C_28,A_22)
      | ~ m1_pre_topc(B_26,A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_447,plain,(
    ! [A_117,B_119,A_118,C_120,C_116] :
      ( m1_pre_topc(k1_tsep_1(A_118,B_119,C_116),C_120)
      | ~ m1_pre_topc(C_120,A_117)
      | ~ m1_pre_topc(k1_tsep_1(A_118,B_119,C_116),A_117)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | ~ r1_tarski(u1_struct_0(C_116),u1_struct_0(C_120))
      | ~ r1_tarski(u1_struct_0(B_119),u1_struct_0(C_120))
      | ~ m1_pre_topc(C_116,A_118)
      | v2_struct_0(C_116)
      | ~ m1_pre_topc(B_119,A_118)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_222,c_16])).

tff(c_459,plain,(
    ! [A_118,B_119,C_116] :
      ( m1_pre_topc(k1_tsep_1(A_118,B_119,C_116),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_118,B_119,C_116),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(u1_struct_0(C_116),u1_struct_0('#skF_3'))
      | ~ r1_tarski(u1_struct_0(B_119),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(C_116,A_118)
      | v2_struct_0(C_116)
      | ~ m1_pre_topc(B_119,A_118)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_28,c_447])).

tff(c_521,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_pre_topc(k1_tsep_1(A_130,B_131,C_132),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_130,B_131,C_132),'#skF_1')
      | ~ r1_tarski(u1_struct_0(C_132),u1_struct_0('#skF_3'))
      | ~ r1_tarski(u1_struct_0(B_131),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(C_132,A_130)
      | v2_struct_0(C_132)
      | ~ m1_pre_topc(B_131,A_130)
      | v2_struct_0(B_131)
      | ~ l1_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_459])).

tff(c_549,plain,(
    ! [A_136,B_137,B_138] :
      ( m1_pre_topc(k1_tsep_1(A_136,B_137,B_138),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_136,B_137,B_138),'#skF_1')
      | ~ r1_tarski(u1_struct_0(B_137),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_138,A_136)
      | v2_struct_0(B_138)
      | ~ m1_pre_topc(B_137,A_136)
      | v2_struct_0(B_137)
      | ~ l1_pre_topc(A_136)
      | v2_struct_0(A_136)
      | ~ m1_pre_topc(B_138,'#skF_3')
      | ~ m1_pre_topc(B_138,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_64,c_521])).

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
    inference(resolution,[status(thm)],[c_64,c_549])).

tff(c_18,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

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
    inference(resolution,[status(thm)],[c_8,c_630])).

tff(c_636,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_24,c_633])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_26,c_636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.53  
% 3.25/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.53  %$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.25/1.53  
% 3.25/1.53  %Foreground sorts:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Background operators:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Foreground operators:
% 3.25/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.25/1.53  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.25/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.25/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.25/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.53  
% 3.25/1.54  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tmap_1)).
% 3.25/1.54  tff(f_82, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 3.25/1.54  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.25/1.54  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 3.25/1.54  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.25/1.54  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_26, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_8, plain, (![A_19, B_20, C_21]: (m1_pre_topc(k1_tsep_1(A_19, B_20, C_21), A_19) | ~m1_pre_topc(C_21, A_19) | v2_struct_0(C_21) | ~m1_pre_topc(B_20, A_19) | v2_struct_0(B_20) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.25/1.54  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_20, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_43, plain, (![B_46, C_47, A_48]: (r1_tarski(u1_struct_0(B_46), u1_struct_0(C_47)) | ~m1_pre_topc(B_46, C_47) | ~m1_pre_topc(C_47, A_48) | ~m1_pre_topc(B_46, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.25/1.54  tff(c_53, plain, (![B_46]: (r1_tarski(u1_struct_0(B_46), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_46, '#skF_3') | ~m1_pre_topc(B_46, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_43])).
% 3.25/1.54  tff(c_64, plain, (![B_46]: (r1_tarski(u1_struct_0(B_46), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_46, '#skF_3') | ~m1_pre_topc(B_46, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_53])).
% 3.25/1.54  tff(c_10, plain, (![A_19, B_20, C_21]: (v1_pre_topc(k1_tsep_1(A_19, B_20, C_21)) | ~m1_pre_topc(C_21, A_19) | v2_struct_0(C_21) | ~m1_pre_topc(B_20, A_19) | v2_struct_0(B_20) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.25/1.54  tff(c_85, plain, (![A_65, B_66, C_67]: (u1_struct_0(k1_tsep_1(A_65, B_66, C_67))=k2_xboole_0(u1_struct_0(B_66), u1_struct_0(C_67)) | ~m1_pre_topc(k1_tsep_1(A_65, B_66, C_67), A_65) | ~v1_pre_topc(k1_tsep_1(A_65, B_66, C_67)) | v2_struct_0(k1_tsep_1(A_65, B_66, C_67)) | ~m1_pre_topc(C_67, A_65) | v2_struct_0(C_67) | ~m1_pre_topc(B_66, A_65) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.54  tff(c_93, plain, (![A_72, B_73, C_74]: (u1_struct_0(k1_tsep_1(A_72, B_73, C_74))=k2_xboole_0(u1_struct_0(B_73), u1_struct_0(C_74)) | ~v1_pre_topc(k1_tsep_1(A_72, B_73, C_74)) | v2_struct_0(k1_tsep_1(A_72, B_73, C_74)) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_8, c_85])).
% 3.25/1.54  tff(c_12, plain, (![A_19, B_20, C_21]: (~v2_struct_0(k1_tsep_1(A_19, B_20, C_21)) | ~m1_pre_topc(C_21, A_19) | v2_struct_0(C_21) | ~m1_pre_topc(B_20, A_19) | v2_struct_0(B_20) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.25/1.54  tff(c_154, plain, (![A_75, B_76, C_77]: (u1_struct_0(k1_tsep_1(A_75, B_76, C_77))=k2_xboole_0(u1_struct_0(B_76), u1_struct_0(C_77)) | ~v1_pre_topc(k1_tsep_1(A_75, B_76, C_77)) | ~m1_pre_topc(C_77, A_75) | v2_struct_0(C_77) | ~m1_pre_topc(B_76, A_75) | v2_struct_0(B_76) | ~l1_pre_topc(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_93, c_12])).
% 3.25/1.54  tff(c_165, plain, (![A_81, B_82, C_83]: (u1_struct_0(k1_tsep_1(A_81, B_82, C_83))=k2_xboole_0(u1_struct_0(B_82), u1_struct_0(C_83)) | ~m1_pre_topc(C_83, A_81) | v2_struct_0(C_83) | ~m1_pre_topc(B_82, A_81) | v2_struct_0(B_82) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_10, c_154])).
% 3.25/1.54  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k2_xboole_0(A_1, C_3), B_2) | ~r1_tarski(C_3, B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.54  tff(c_222, plain, (![A_84, B_85, C_86, B_87]: (r1_tarski(u1_struct_0(k1_tsep_1(A_84, B_85, C_86)), B_87) | ~r1_tarski(u1_struct_0(C_86), B_87) | ~r1_tarski(u1_struct_0(B_85), B_87) | ~m1_pre_topc(C_86, A_84) | v2_struct_0(C_86) | ~m1_pre_topc(B_85, A_84) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_165, c_2])).
% 3.25/1.54  tff(c_16, plain, (![B_26, C_28, A_22]: (m1_pre_topc(B_26, C_28) | ~r1_tarski(u1_struct_0(B_26), u1_struct_0(C_28)) | ~m1_pre_topc(C_28, A_22) | ~m1_pre_topc(B_26, A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.25/1.54  tff(c_447, plain, (![A_117, B_119, A_118, C_120, C_116]: (m1_pre_topc(k1_tsep_1(A_118, B_119, C_116), C_120) | ~m1_pre_topc(C_120, A_117) | ~m1_pre_topc(k1_tsep_1(A_118, B_119, C_116), A_117) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | ~r1_tarski(u1_struct_0(C_116), u1_struct_0(C_120)) | ~r1_tarski(u1_struct_0(B_119), u1_struct_0(C_120)) | ~m1_pre_topc(C_116, A_118) | v2_struct_0(C_116) | ~m1_pre_topc(B_119, A_118) | v2_struct_0(B_119) | ~l1_pre_topc(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_222, c_16])).
% 3.25/1.54  tff(c_459, plain, (![A_118, B_119, C_116]: (m1_pre_topc(k1_tsep_1(A_118, B_119, C_116), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_118, B_119, C_116), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(u1_struct_0(C_116), u1_struct_0('#skF_3')) | ~r1_tarski(u1_struct_0(B_119), u1_struct_0('#skF_3')) | ~m1_pre_topc(C_116, A_118) | v2_struct_0(C_116) | ~m1_pre_topc(B_119, A_118) | v2_struct_0(B_119) | ~l1_pre_topc(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_28, c_447])).
% 3.25/1.54  tff(c_521, plain, (![A_130, B_131, C_132]: (m1_pre_topc(k1_tsep_1(A_130, B_131, C_132), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_130, B_131, C_132), '#skF_1') | ~r1_tarski(u1_struct_0(C_132), u1_struct_0('#skF_3')) | ~r1_tarski(u1_struct_0(B_131), u1_struct_0('#skF_3')) | ~m1_pre_topc(C_132, A_130) | v2_struct_0(C_132) | ~m1_pre_topc(B_131, A_130) | v2_struct_0(B_131) | ~l1_pre_topc(A_130) | v2_struct_0(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_459])).
% 3.25/1.54  tff(c_549, plain, (![A_136, B_137, B_138]: (m1_pre_topc(k1_tsep_1(A_136, B_137, B_138), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_136, B_137, B_138), '#skF_1') | ~r1_tarski(u1_struct_0(B_137), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_138, A_136) | v2_struct_0(B_138) | ~m1_pre_topc(B_137, A_136) | v2_struct_0(B_137) | ~l1_pre_topc(A_136) | v2_struct_0(A_136) | ~m1_pre_topc(B_138, '#skF_3') | ~m1_pre_topc(B_138, '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_521])).
% 3.25/1.54  tff(c_609, plain, (![A_152, B_153, B_154]: (m1_pre_topc(k1_tsep_1(A_152, B_153, B_154), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_152, B_153, B_154), '#skF_1') | ~m1_pre_topc(B_154, A_152) | v2_struct_0(B_154) | ~m1_pre_topc(B_153, A_152) | v2_struct_0(B_153) | ~l1_pre_topc(A_152) | v2_struct_0(A_152) | ~m1_pre_topc(B_154, '#skF_3') | ~m1_pre_topc(B_154, '#skF_1') | ~m1_pre_topc(B_153, '#skF_3') | ~m1_pre_topc(B_153, '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_549])).
% 3.25/1.54  tff(c_18, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.54  tff(c_620, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_609, c_18])).
% 3.25/1.54  tff(c_629, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22, c_24, c_20, c_36, c_620])).
% 3.25/1.54  tff(c_630, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_26, c_629])).
% 3.25/1.54  tff(c_633, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_630])).
% 3.25/1.54  tff(c_636, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_24, c_633])).
% 3.25/1.54  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_26, c_636])).
% 3.25/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.54  
% 3.25/1.54  Inference rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Ref     : 0
% 3.25/1.54  #Sup     : 185
% 3.25/1.54  #Fact    : 0
% 3.25/1.54  #Define  : 0
% 3.25/1.54  #Split   : 4
% 3.25/1.54  #Chain   : 0
% 3.25/1.54  #Close   : 0
% 3.25/1.54  
% 3.25/1.54  Ordering : KBO
% 3.25/1.54  
% 3.25/1.54  Simplification rules
% 3.25/1.54  ----------------------
% 3.25/1.54  #Subsume      : 38
% 3.25/1.54  #Demod        : 27
% 3.25/1.54  #Tautology    : 8
% 3.25/1.54  #SimpNegUnit  : 9
% 3.25/1.54  #BackRed      : 0
% 3.25/1.54  
% 3.25/1.54  #Partial instantiations: 0
% 3.25/1.54  #Strategies tried      : 1
% 3.25/1.54  
% 3.25/1.54  Timing (in seconds)
% 3.25/1.54  ----------------------
% 3.25/1.54  Preprocessing        : 0.30
% 3.25/1.54  Parsing              : 0.16
% 3.25/1.54  CNF conversion       : 0.02
% 3.25/1.54  Main loop            : 0.47
% 3.25/1.55  Inferencing          : 0.18
% 3.25/1.55  Reduction            : 0.12
% 3.25/1.55  Demodulation         : 0.08
% 3.25/1.55  BG Simplification    : 0.03
% 3.25/1.55  Subsumption          : 0.13
% 3.25/1.55  Abstraction          : 0.03
% 3.25/1.55  MUC search           : 0.00
% 3.25/1.55  Cooper               : 0.00
% 3.25/1.55  Total                : 0.80
% 3.25/1.55  Index Insertion      : 0.00
% 3.25/1.55  Index Deletion       : 0.00
% 3.25/1.55  Index Matching       : 0.00
% 3.25/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

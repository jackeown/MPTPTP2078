%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:18 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 149 expanded)
%              Number of leaves         :   37 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 315 expanded)
%              Number of equality atoms :   48 ( 205 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_72,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_99,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_166,plain,(
    ! [A_77,B_78] :
      ( r1_xboole_0(k1_tarski(A_77),B_78)
      | r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [B_78,A_77] :
      ( r1_xboole_0(B_78,k1_tarski(A_77))
      | r2_hidden(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_166,c_10])).

tff(c_76,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_480,plain,(
    ! [A_116,B_117,C_118] :
      ( r1_xboole_0(A_116,B_117)
      | ~ r1_xboole_0(A_116,k2_xboole_0(B_117,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_498,plain,(
    ! [A_119] :
      ( r1_xboole_0(A_119,'#skF_3')
      | ~ r1_xboole_0(A_119,k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_480])).

tff(c_509,plain,(
    ! [B_120] :
      ( r1_xboole_0(B_120,'#skF_3')
      | r2_hidden('#skF_2',B_120) ) ),
    inference(resolution,[status(thm)],[c_173,c_498])).

tff(c_54,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tarski(A_52),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_70,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_94,plain,(
    k1_tarski('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_95,plain,(
    ! [A_65,B_66] : r1_tarski(A_65,k2_xboole_0(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_98,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_95])).

tff(c_391,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_397,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_391])).

tff(c_408,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_397])).

tff(c_466,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_408])).

tff(c_517,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_509,c_466])).

tff(c_28,plain,(
    ! [A_18] :
      ( ~ r1_xboole_0(A_18,A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_531,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_517,c_28])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_531])).

tff(c_538,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_820,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_1'(A_164,B_165),A_164)
      | r1_tarski(A_164,B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_539,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_710,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = '#skF_3'
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_20])).

tff(c_730,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_710])).

tff(c_66,plain,(
    ! [B_61] : k4_xboole_0(k1_tarski(B_61),k1_tarski(B_61)) != k1_tarski(B_61) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_741,plain,(
    ! [B_61] : k1_tarski(B_61) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_66])).

tff(c_62,plain,(
    ! [B_57] : r1_tarski(k1_xboole_0,k1_tarski(B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_540,plain,(
    ! [B_57] : r1_tarski('#skF_3',k1_tarski(B_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_62])).

tff(c_757,plain,(
    ! [B_155,A_156] :
      ( B_155 = A_156
      | ~ r1_tarski(B_155,A_156)
      | ~ r1_tarski(A_156,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_763,plain,(
    ! [B_57] :
      ( k1_tarski(B_57) = '#skF_3'
      | ~ r1_tarski(k1_tarski(B_57),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_540,c_757])).

tff(c_778,plain,(
    ! [B_157] : ~ r1_tarski(k1_tarski(B_157),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_763])).

tff(c_787,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_778])).

tff(c_827,plain,(
    ! [B_166] : r1_tarski('#skF_3',B_166) ),
    inference(resolution,[status(thm)],[c_820,c_787])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_838,plain,(
    ! [B_166] : k2_xboole_0('#skF_3',B_166) = B_166 ),
    inference(resolution,[status(thm)],[c_827,c_24])).

tff(c_864,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_76])).

tff(c_866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_864])).

tff(c_868,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_902,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_868,c_74])).

tff(c_867,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1145,plain,(
    ! [A_193,B_194] :
      ( r1_xboole_0(k1_tarski(A_193),B_194)
      | r2_hidden(A_193,B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1154,plain,(
    ! [B_194] :
      ( r1_xboole_0('#skF_3',B_194)
      | r2_hidden('#skF_2',B_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_1145])).

tff(c_1173,plain,(
    ! [A_199,B_200] :
      ( r1_tarski(k1_tarski(A_199),B_200)
      | ~ r2_hidden(A_199,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1185,plain,(
    ! [B_201] :
      ( r1_tarski('#skF_3',B_201)
      | ~ r2_hidden('#skF_2',B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_1173])).

tff(c_1201,plain,(
    ! [B_202] :
      ( r1_tarski('#skF_3',B_202)
      | r1_xboole_0('#skF_3',B_202) ) ),
    inference(resolution,[status(thm)],[c_1154,c_1185])).

tff(c_1208,plain,(
    ! [B_202] :
      ( r1_xboole_0(B_202,'#skF_3')
      | r1_tarski('#skF_3',B_202) ) ),
    inference(resolution,[status(thm)],[c_1201,c_10])).

tff(c_870,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_76])).

tff(c_1308,plain,(
    ! [A_217,C_218,B_219] :
      ( r1_xboole_0(A_217,C_218)
      | ~ r1_xboole_0(A_217,k2_xboole_0(B_219,C_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1331,plain,(
    ! [A_220] :
      ( r1_xboole_0(A_220,'#skF_4')
      | ~ r1_xboole_0(A_220,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_1308])).

tff(c_1347,plain,(
    ! [B_221] :
      ( r1_xboole_0(B_221,'#skF_4')
      | r1_tarski('#skF_3',B_221) ) ),
    inference(resolution,[status(thm)],[c_1208,c_1331])).

tff(c_1353,plain,
    ( k1_xboole_0 = '#skF_4'
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1347,c_28])).

tff(c_1357,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_867,c_1353])).

tff(c_1364,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1357,c_24])).

tff(c_1552,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_870])).

tff(c_1554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_902,c_1552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:03:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.54  
% 3.32/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/1.54  
% 3.32/1.54  %Foreground sorts:
% 3.32/1.54  
% 3.32/1.54  
% 3.32/1.54  %Background operators:
% 3.32/1.54  
% 3.32/1.54  
% 3.32/1.54  %Foreground operators:
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.32/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.54  
% 3.49/1.56  tff(f_139, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.49/1.56  tff(f_107, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.49/1.56  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.49/1.56  tff(f_82, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.49/1.56  tff(f_102, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.49/1.56  tff(f_84, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.49/1.56  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.49/1.56  tff(f_66, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.49/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.49/1.56  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.49/1.56  tff(f_120, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.49/1.56  tff(f_113, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.49/1.56  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.49/1.56  tff(c_72, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.49/1.56  tff(c_99, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_72])).
% 3.49/1.56  tff(c_166, plain, (![A_77, B_78]: (r1_xboole_0(k1_tarski(A_77), B_78) | r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.56  tff(c_10, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.56  tff(c_173, plain, (![B_78, A_77]: (r1_xboole_0(B_78, k1_tarski(A_77)) | r2_hidden(A_77, B_78))), inference(resolution, [status(thm)], [c_166, c_10])).
% 3.49/1.56  tff(c_76, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.49/1.56  tff(c_480, plain, (![A_116, B_117, C_118]: (r1_xboole_0(A_116, B_117) | ~r1_xboole_0(A_116, k2_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.49/1.56  tff(c_498, plain, (![A_119]: (r1_xboole_0(A_119, '#skF_3') | ~r1_xboole_0(A_119, k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_480])).
% 3.49/1.56  tff(c_509, plain, (![B_120]: (r1_xboole_0(B_120, '#skF_3') | r2_hidden('#skF_2', B_120))), inference(resolution, [status(thm)], [c_173, c_498])).
% 3.49/1.56  tff(c_54, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.56  tff(c_70, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.49/1.56  tff(c_94, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 3.49/1.56  tff(c_95, plain, (![A_65, B_66]: (r1_tarski(A_65, k2_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.49/1.56  tff(c_98, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_95])).
% 3.49/1.56  tff(c_391, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.49/1.56  tff(c_397, plain, (k1_tarski('#skF_2')='#skF_3' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_98, c_391])).
% 3.49/1.56  tff(c_408, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_94, c_397])).
% 3.49/1.56  tff(c_466, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_408])).
% 3.49/1.56  tff(c_517, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_509, c_466])).
% 3.49/1.56  tff(c_28, plain, (![A_18]: (~r1_xboole_0(A_18, A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.49/1.56  tff(c_531, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_517, c_28])).
% 3.49/1.56  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_531])).
% 3.49/1.56  tff(c_538, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_72])).
% 3.49/1.56  tff(c_820, plain, (![A_164, B_165]: (r2_hidden('#skF_1'(A_164, B_165), A_164) | r1_tarski(A_164, B_165))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.56  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.49/1.56  tff(c_539, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 3.49/1.56  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.49/1.56  tff(c_710, plain, (![A_148, B_149]: (k4_xboole_0(A_148, B_149)='#skF_3' | ~r1_tarski(A_148, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_20])).
% 3.49/1.56  tff(c_730, plain, (![B_11]: (k4_xboole_0(B_11, B_11)='#skF_3')), inference(resolution, [status(thm)], [c_16, c_710])).
% 3.49/1.56  tff(c_66, plain, (![B_61]: (k4_xboole_0(k1_tarski(B_61), k1_tarski(B_61))!=k1_tarski(B_61))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.56  tff(c_741, plain, (![B_61]: (k1_tarski(B_61)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_66])).
% 3.49/1.56  tff(c_62, plain, (![B_57]: (r1_tarski(k1_xboole_0, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.49/1.56  tff(c_540, plain, (![B_57]: (r1_tarski('#skF_3', k1_tarski(B_57)))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_62])).
% 3.49/1.56  tff(c_757, plain, (![B_155, A_156]: (B_155=A_156 | ~r1_tarski(B_155, A_156) | ~r1_tarski(A_156, B_155))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.49/1.56  tff(c_763, plain, (![B_57]: (k1_tarski(B_57)='#skF_3' | ~r1_tarski(k1_tarski(B_57), '#skF_3'))), inference(resolution, [status(thm)], [c_540, c_757])).
% 3.49/1.56  tff(c_778, plain, (![B_157]: (~r1_tarski(k1_tarski(B_157), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_741, c_763])).
% 3.49/1.56  tff(c_787, plain, (![A_52]: (~r2_hidden(A_52, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_778])).
% 3.49/1.56  tff(c_827, plain, (![B_166]: (r1_tarski('#skF_3', B_166))), inference(resolution, [status(thm)], [c_820, c_787])).
% 3.49/1.56  tff(c_24, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.56  tff(c_838, plain, (![B_166]: (k2_xboole_0('#skF_3', B_166)=B_166)), inference(resolution, [status(thm)], [c_827, c_24])).
% 3.49/1.56  tff(c_864, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_838, c_76])).
% 3.49/1.56  tff(c_866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_538, c_864])).
% 3.49/1.56  tff(c_868, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 3.49/1.56  tff(c_74, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.49/1.56  tff(c_902, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_868, c_868, c_74])).
% 3.49/1.56  tff(c_867, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 3.49/1.56  tff(c_1145, plain, (![A_193, B_194]: (r1_xboole_0(k1_tarski(A_193), B_194) | r2_hidden(A_193, B_194))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.56  tff(c_1154, plain, (![B_194]: (r1_xboole_0('#skF_3', B_194) | r2_hidden('#skF_2', B_194))), inference(superposition, [status(thm), theory('equality')], [c_868, c_1145])).
% 3.49/1.56  tff(c_1173, plain, (![A_199, B_200]: (r1_tarski(k1_tarski(A_199), B_200) | ~r2_hidden(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.56  tff(c_1185, plain, (![B_201]: (r1_tarski('#skF_3', B_201) | ~r2_hidden('#skF_2', B_201))), inference(superposition, [status(thm), theory('equality')], [c_868, c_1173])).
% 3.49/1.56  tff(c_1201, plain, (![B_202]: (r1_tarski('#skF_3', B_202) | r1_xboole_0('#skF_3', B_202))), inference(resolution, [status(thm)], [c_1154, c_1185])).
% 3.49/1.56  tff(c_1208, plain, (![B_202]: (r1_xboole_0(B_202, '#skF_3') | r1_tarski('#skF_3', B_202))), inference(resolution, [status(thm)], [c_1201, c_10])).
% 3.49/1.56  tff(c_870, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_868, c_76])).
% 3.49/1.56  tff(c_1308, plain, (![A_217, C_218, B_219]: (r1_xboole_0(A_217, C_218) | ~r1_xboole_0(A_217, k2_xboole_0(B_219, C_218)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.49/1.56  tff(c_1331, plain, (![A_220]: (r1_xboole_0(A_220, '#skF_4') | ~r1_xboole_0(A_220, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_870, c_1308])).
% 3.49/1.56  tff(c_1347, plain, (![B_221]: (r1_xboole_0(B_221, '#skF_4') | r1_tarski('#skF_3', B_221))), inference(resolution, [status(thm)], [c_1208, c_1331])).
% 3.49/1.56  tff(c_1353, plain, (k1_xboole_0='#skF_4' | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1347, c_28])).
% 3.49/1.56  tff(c_1357, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_867, c_1353])).
% 3.49/1.56  tff(c_1364, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1357, c_24])).
% 3.49/1.56  tff(c_1552, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_870])).
% 3.49/1.56  tff(c_1554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_902, c_1552])).
% 3.49/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.56  
% 3.49/1.56  Inference rules
% 3.49/1.56  ----------------------
% 3.49/1.56  #Ref     : 0
% 3.49/1.56  #Sup     : 338
% 3.49/1.56  #Fact    : 0
% 3.49/1.56  #Define  : 0
% 3.49/1.56  #Split   : 3
% 3.49/1.56  #Chain   : 0
% 3.49/1.56  #Close   : 0
% 3.49/1.56  
% 3.49/1.56  Ordering : KBO
% 3.49/1.56  
% 3.49/1.56  Simplification rules
% 3.49/1.56  ----------------------
% 3.49/1.56  #Subsume      : 13
% 3.49/1.56  #Demod        : 116
% 3.49/1.56  #Tautology    : 214
% 3.49/1.56  #SimpNegUnit  : 17
% 3.49/1.56  #BackRed      : 18
% 3.49/1.56  
% 3.49/1.56  #Partial instantiations: 0
% 3.49/1.56  #Strategies tried      : 1
% 3.49/1.56  
% 3.49/1.56  Timing (in seconds)
% 3.49/1.56  ----------------------
% 3.49/1.56  Preprocessing        : 0.34
% 3.49/1.56  Parsing              : 0.18
% 3.49/1.56  CNF conversion       : 0.02
% 3.49/1.56  Main loop            : 0.43
% 3.49/1.56  Inferencing          : 0.16
% 3.49/1.56  Reduction            : 0.13
% 3.49/1.56  Demodulation         : 0.09
% 3.49/1.56  BG Simplification    : 0.02
% 3.49/1.56  Subsumption          : 0.07
% 3.49/1.56  Abstraction          : 0.02
% 3.49/1.56  MUC search           : 0.00
% 3.49/1.56  Cooper               : 0.00
% 3.49/1.56  Total                : 0.81
% 3.49/1.56  Index Insertion      : 0.00
% 3.49/1.56  Index Deletion       : 0.00
% 3.49/1.56  Index Matching       : 0.00
% 3.49/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------

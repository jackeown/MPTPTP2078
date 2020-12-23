%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:13 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 523 expanded)
%              Number of leaves         :   47 ( 193 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 ( 858 expanded)
%              Number of equality atoms :   85 ( 576 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_110,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_108,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_137,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_119,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_104,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_92,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_88,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_135,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_92,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_148,plain,(
    ! [A_90,B_91] : r1_tarski(A_90,k2_xboole_0(A_90,B_91)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_151,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_148])).

tff(c_284,plain,(
    ! [A_114,B_115] :
      ( k2_xboole_0(A_114,B_115) = B_115
      | ~ r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_302,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_151,c_284])).

tff(c_20,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [A_40] : k5_xboole_0(A_40,A_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18,plain,(
    ! [A_14] : k2_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1057,plain,(
    ! [A_189,B_190] : k5_xboole_0(k5_xboole_0(A_189,B_190),k2_xboole_0(A_189,B_190)) = k3_xboole_0(A_189,B_190) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1115,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,A_14),A_14) = k3_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1057])).

tff(c_1123,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_50,c_1115])).

tff(c_809,plain,(
    ! [A_173,B_174,C_175] : k5_xboole_0(k5_xboole_0(A_173,B_174),C_175) = k5_xboole_0(A_173,k5_xboole_0(B_174,C_175)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_848,plain,(
    ! [A_40,C_175] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_175)) = k5_xboole_0(k1_xboole_0,C_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_809])).

tff(c_1613,plain,(
    ! [A_40,C_175] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_175)) = C_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_848])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1614,plain,(
    ! [A_223,C_224] : k5_xboole_0(A_223,k5_xboole_0(A_223,C_224)) = C_224 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_848])).

tff(c_1795,plain,(
    ! [A_226,B_227] : k5_xboole_0(A_226,k5_xboole_0(B_227,A_226)) = B_227 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1614])).

tff(c_1834,plain,(
    ! [A_40,C_175] : k5_xboole_0(k5_xboole_0(A_40,C_175),C_175) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_1795])).

tff(c_46,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2214,plain,(
    ! [A_239,B_240] : k2_xboole_0(A_239,k2_xboole_0(A_239,B_240)) = k2_xboole_0(A_239,B_240) ),
    inference(resolution,[status(thm)],[c_46,c_284])).

tff(c_52,plain,(
    ! [A_41,B_42] : k5_xboole_0(k5_xboole_0(A_41,B_42),k2_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2223,plain,(
    ! [A_239,B_240] : k5_xboole_0(k5_xboole_0(A_239,k2_xboole_0(A_239,B_240)),k2_xboole_0(A_239,B_240)) = k3_xboole_0(A_239,k2_xboole_0(A_239,B_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2214,c_52])).

tff(c_2294,plain,(
    ! [A_246,B_247] : k3_xboole_0(A_246,k2_xboole_0(A_246,B_247)) = A_246 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_2223])).

tff(c_2354,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_2294])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_423,plain,(
    ! [A_140,B_141,C_142] :
      ( ~ r1_xboole_0(A_140,B_141)
      | ~ r2_hidden(C_142,k3_xboole_0(A_140,B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_446,plain,(
    ! [A_140,B_141] :
      ( ~ r1_xboole_0(A_140,B_141)
      | v1_xboole_0(k3_xboole_0(A_140,B_141)) ) ),
    inference(resolution,[status(thm)],[c_6,c_423])).

tff(c_2385,plain,
    ( ~ r1_xboole_0('#skF_8',k1_tarski('#skF_7'))
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2354,c_446])).

tff(c_2424,plain,(
    ~ r1_xboole_0('#skF_8',k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2385])).

tff(c_82,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tarski(A_76),B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_86,plain,
    ( k1_xboole_0 != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_130,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_496,plain,(
    ! [B_146,A_147] :
      ( B_146 = A_147
      | ~ r1_tarski(B_146,A_147)
      | ~ r1_tarski(A_147,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_504,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_151,c_496])).

tff(c_514,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_504])).

tff(c_566,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_514])).

tff(c_375,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_3'(A_128,B_129),B_129)
      | r1_xboole_0(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [C_47,A_43] :
      ( C_47 = A_43
      | ~ r2_hidden(C_47,k1_tarski(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4045,plain,(
    ! [A_354,A_355] :
      ( '#skF_3'(A_354,k1_tarski(A_355)) = A_355
      | r1_xboole_0(A_354,k1_tarski(A_355)) ) ),
    inference(resolution,[status(thm)],[c_375,c_54])).

tff(c_4081,plain,(
    '#skF_3'('#skF_8',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_4045,c_2424])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_3'(A_18,B_19),A_18)
      | r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4098,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r1_xboole_0('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4081,c_26])).

tff(c_4104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2424,c_566,c_4098])).

tff(c_4105,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2385])).

tff(c_354,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_3'(A_123,B_124),A_123)
      | r1_xboole_0(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_364,plain,(
    ! [A_125,B_126] :
      ( ~ v1_xboole_0(A_125)
      | r1_xboole_0(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_354,c_4])).

tff(c_44,plain,(
    ! [A_34] :
      ( ~ r1_xboole_0(A_34,A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_373,plain,(
    ! [B_126] :
      ( k1_xboole_0 = B_126
      | ~ v1_xboole_0(B_126) ) ),
    inference(resolution,[status(thm)],[c_364,c_44])).

tff(c_4121,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4105,c_373])).

tff(c_4131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_4121])).

tff(c_4132,plain,(
    k1_tarski('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_4133,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_42,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4135,plain,(
    r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4133,c_4133,c_42])).

tff(c_4388,plain,(
    ! [A_398,B_399,C_400] :
      ( ~ r1_xboole_0(A_398,B_399)
      | ~ r2_hidden(C_400,k3_xboole_0(A_398,B_399)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4434,plain,(
    ! [A_403,C_404] :
      ( ~ r1_xboole_0(A_403,A_403)
      | ~ r2_hidden(C_404,A_403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4388])).

tff(c_4443,plain,(
    ! [C_405] : ~ r2_hidden(C_405,'#skF_8') ),
    inference(resolution,[status(thm)],[c_4135,c_4434])).

tff(c_4453,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_4443])).

tff(c_4367,plain,(
    ! [A_392,B_393] :
      ( r2_hidden('#skF_2'(A_392,B_393),A_392)
      | r1_tarski(A_392,B_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4377,plain,(
    ! [A_394,B_395] :
      ( ~ v1_xboole_0(A_394)
      | r1_tarski(A_394,B_395) ) ),
    inference(resolution,[status(thm)],[c_4367,c_4])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4386,plain,(
    ! [A_394,B_395] :
      ( k2_xboole_0(A_394,B_395) = B_395
      | ~ v1_xboole_0(A_394) ) ),
    inference(resolution,[status(thm)],[c_4377,c_38])).

tff(c_4456,plain,(
    ! [B_395] : k2_xboole_0('#skF_8',B_395) = B_395 ),
    inference(resolution,[status(thm)],[c_4453,c_4386])).

tff(c_4474,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4456,c_92])).

tff(c_4476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4132,c_4474])).

tff(c_4477,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6253,plain,(
    ! [A_559,B_560] : k5_xboole_0(k5_xboole_0(A_559,B_560),k2_xboole_0(A_559,B_560)) = k3_xboole_0(A_559,B_560) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6295,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,A_14),A_14) = k3_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6253])).

tff(c_6303,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20,c_6295])).

tff(c_6861,plain,(
    ! [A_576,B_577,C_578] : k5_xboole_0(k5_xboole_0(A_576,B_577),C_578) = k5_xboole_0(A_576,k5_xboole_0(B_577,C_578)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6950,plain,(
    ! [A_40,C_578] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_578)) = k5_xboole_0(k1_xboole_0,C_578) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_6861])).

tff(c_6967,plain,(
    ! [A_40,C_578] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_578)) = C_578 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6303,c_6950])).

tff(c_4478,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4483,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_92])).

tff(c_6292,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8','#skF_9'),'#skF_8') = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4483,c_6253])).

tff(c_6407,plain,(
    k5_xboole_0('#skF_8',k5_xboole_0('#skF_8','#skF_9')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6292])).

tff(c_6982,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6967,c_6407])).

tff(c_4841,plain,(
    ! [A_453,B_454,C_455] :
      ( ~ r1_xboole_0(A_453,B_454)
      | ~ r2_hidden(C_455,k3_xboole_0(A_453,B_454)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4854,plain,(
    ! [A_453,B_454] :
      ( ~ r1_xboole_0(A_453,B_454)
      | v1_xboole_0(k3_xboole_0(A_453,B_454)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4841])).

tff(c_7074,plain,
    ( ~ r1_xboole_0('#skF_8','#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_6982,c_4854])).

tff(c_7422,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_7074])).

tff(c_90,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4525,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4478,c_4478,c_90])).

tff(c_40,plain,(
    ! [A_32,B_33] : r1_tarski(k3_xboole_0(A_32,B_33),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7092,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_6982,c_40])).

tff(c_32,plain,(
    ! [B_29,A_28] :
      ( B_29 = A_28
      | ~ r1_tarski(B_29,A_28)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7157,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_7092,c_32])).

tff(c_7169,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_4525,c_7157])).

tff(c_5392,plain,(
    ! [A_499,B_500] :
      ( r2_hidden('#skF_2'(A_499,B_500),A_499)
      | r1_tarski(A_499,B_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4536,plain,(
    ! [C_418,A_419] :
      ( C_418 = A_419
      | ~ r2_hidden(C_418,k1_tarski(A_419)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4543,plain,(
    ! [C_418] :
      ( C_418 = '#skF_7'
      | ~ r2_hidden(C_418,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4478,c_4536])).

tff(c_5425,plain,(
    ! [B_500] :
      ( '#skF_2'('#skF_8',B_500) = '#skF_7'
      | r1_tarski('#skF_8',B_500) ) ),
    inference(resolution,[status(thm)],[c_5392,c_4543])).

tff(c_7180,plain,(
    '#skF_2'('#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5425,c_7169])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7402,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7180,c_10])).

tff(c_7410,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_7169,c_7402])).

tff(c_4908,plain,(
    ! [A_464,B_465] :
      ( r2_hidden('#skF_3'(A_464,B_465),A_464)
      | r1_xboole_0(A_464,B_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4934,plain,(
    ! [B_465] :
      ( '#skF_3'('#skF_8',B_465) = '#skF_7'
      | r1_xboole_0('#skF_8',B_465) ) ),
    inference(resolution,[status(thm)],[c_4908,c_4543])).

tff(c_7443,plain,(
    '#skF_3'('#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_4934,c_7422])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_3'(A_18,B_19),B_19)
      | r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7455,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7443,c_24])).

tff(c_7462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7422,c_7410,c_7455])).

tff(c_7463,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_7074])).

tff(c_5026,plain,(
    ! [A_471,B_472] :
      ( ~ v1_xboole_0(A_471)
      | r1_xboole_0(A_471,B_472) ) ),
    inference(resolution,[status(thm)],[c_4908,c_4])).

tff(c_5039,plain,(
    ! [B_472] :
      ( k1_xboole_0 = B_472
      | ~ v1_xboole_0(B_472) ) ),
    inference(resolution,[status(thm)],[c_5026,c_44])).

tff(c_7482,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7463,c_5039])).

tff(c_7494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4477,c_7482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.41  
% 7.05/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 7.05/2.41  
% 7.05/2.41  %Foreground sorts:
% 7.05/2.41  
% 7.05/2.41  
% 7.05/2.41  %Background operators:
% 7.05/2.41  
% 7.05/2.41  
% 7.05/2.41  %Foreground operators:
% 7.05/2.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.05/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.05/2.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.05/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.05/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.05/2.41  tff('#skF_7', type, '#skF_7': $i).
% 7.05/2.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.05/2.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.05/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.05/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.05/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.05/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.05/2.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.05/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.41  tff('#skF_9', type, '#skF_9': $i).
% 7.05/2.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.41  tff('#skF_8', type, '#skF_8': $i).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.05/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.05/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.05/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.05/2.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.05/2.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.05/2.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.05/2.41  
% 7.05/2.44  tff(f_158, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 7.05/2.44  tff(f_106, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.05/2.44  tff(f_90, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.05/2.44  tff(f_48, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.05/2.44  tff(f_110, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.05/2.44  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.05/2.44  tff(f_112, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.05/2.44  tff(f_108, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.05/2.44  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.05/2.44  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.05/2.44  tff(f_80, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.05/2.44  tff(f_137, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.05/2.44  tff(f_86, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.05/2.44  tff(f_66, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.05/2.44  tff(f_119, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.05/2.44  tff(f_104, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 7.05/2.44  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.05/2.44  tff(f_92, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.05/2.44  tff(c_88, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.05/2.44  tff(c_135, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_88])).
% 7.05/2.44  tff(c_92, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.05/2.44  tff(c_148, plain, (![A_90, B_91]: (r1_tarski(A_90, k2_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.05/2.44  tff(c_151, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_148])).
% 7.05/2.44  tff(c_284, plain, (![A_114, B_115]: (k2_xboole_0(A_114, B_115)=B_115 | ~r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.05/2.44  tff(c_302, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_151, c_284])).
% 7.05/2.44  tff(c_20, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.05/2.44  tff(c_50, plain, (![A_40]: (k5_xboole_0(A_40, A_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.05/2.44  tff(c_18, plain, (![A_14]: (k2_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.05/2.44  tff(c_1057, plain, (![A_189, B_190]: (k5_xboole_0(k5_xboole_0(A_189, B_190), k2_xboole_0(A_189, B_190))=k3_xboole_0(A_189, B_190))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_1115, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, A_14), A_14)=k3_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1057])).
% 7.05/2.44  tff(c_1123, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_50, c_1115])).
% 7.05/2.44  tff(c_809, plain, (![A_173, B_174, C_175]: (k5_xboole_0(k5_xboole_0(A_173, B_174), C_175)=k5_xboole_0(A_173, k5_xboole_0(B_174, C_175)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.05/2.44  tff(c_848, plain, (![A_40, C_175]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_175))=k5_xboole_0(k1_xboole_0, C_175))), inference(superposition, [status(thm), theory('equality')], [c_50, c_809])).
% 7.05/2.44  tff(c_1613, plain, (![A_40, C_175]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_175))=C_175)), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_848])).
% 7.05/2.44  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.05/2.44  tff(c_1614, plain, (![A_223, C_224]: (k5_xboole_0(A_223, k5_xboole_0(A_223, C_224))=C_224)), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_848])).
% 7.05/2.44  tff(c_1795, plain, (![A_226, B_227]: (k5_xboole_0(A_226, k5_xboole_0(B_227, A_226))=B_227)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1614])).
% 7.05/2.44  tff(c_1834, plain, (![A_40, C_175]: (k5_xboole_0(k5_xboole_0(A_40, C_175), C_175)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_1613, c_1795])).
% 7.05/2.44  tff(c_46, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.05/2.44  tff(c_2214, plain, (![A_239, B_240]: (k2_xboole_0(A_239, k2_xboole_0(A_239, B_240))=k2_xboole_0(A_239, B_240))), inference(resolution, [status(thm)], [c_46, c_284])).
% 7.05/2.44  tff(c_52, plain, (![A_41, B_42]: (k5_xboole_0(k5_xboole_0(A_41, B_42), k2_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_2223, plain, (![A_239, B_240]: (k5_xboole_0(k5_xboole_0(A_239, k2_xboole_0(A_239, B_240)), k2_xboole_0(A_239, B_240))=k3_xboole_0(A_239, k2_xboole_0(A_239, B_240)))), inference(superposition, [status(thm), theory('equality')], [c_2214, c_52])).
% 7.05/2.44  tff(c_2294, plain, (![A_246, B_247]: (k3_xboole_0(A_246, k2_xboole_0(A_246, B_247))=A_246)), inference(demodulation, [status(thm), theory('equality')], [c_1834, c_2223])).
% 7.05/2.44  tff(c_2354, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_302, c_2294])).
% 7.05/2.44  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.05/2.44  tff(c_423, plain, (![A_140, B_141, C_142]: (~r1_xboole_0(A_140, B_141) | ~r2_hidden(C_142, k3_xboole_0(A_140, B_141)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_446, plain, (![A_140, B_141]: (~r1_xboole_0(A_140, B_141) | v1_xboole_0(k3_xboole_0(A_140, B_141)))), inference(resolution, [status(thm)], [c_6, c_423])).
% 7.05/2.44  tff(c_2385, plain, (~r1_xboole_0('#skF_8', k1_tarski('#skF_7')) | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2354, c_446])).
% 7.05/2.44  tff(c_2424, plain, (~r1_xboole_0('#skF_8', k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_2385])).
% 7.05/2.44  tff(c_82, plain, (![A_76, B_77]: (r1_tarski(k1_tarski(A_76), B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.05/2.44  tff(c_86, plain, (k1_xboole_0!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.05/2.44  tff(c_130, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_86])).
% 7.05/2.44  tff(c_496, plain, (![B_146, A_147]: (B_146=A_147 | ~r1_tarski(B_146, A_147) | ~r1_tarski(A_147, B_146))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.05/2.44  tff(c_504, plain, (k1_tarski('#skF_7')='#skF_8' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_151, c_496])).
% 7.05/2.44  tff(c_514, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_130, c_504])).
% 7.05/2.44  tff(c_566, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_82, c_514])).
% 7.05/2.44  tff(c_375, plain, (![A_128, B_129]: (r2_hidden('#skF_3'(A_128, B_129), B_129) | r1_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.05/2.44  tff(c_54, plain, (![C_47, A_43]: (C_47=A_43 | ~r2_hidden(C_47, k1_tarski(A_43)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.44  tff(c_4045, plain, (![A_354, A_355]: ('#skF_3'(A_354, k1_tarski(A_355))=A_355 | r1_xboole_0(A_354, k1_tarski(A_355)))), inference(resolution, [status(thm)], [c_375, c_54])).
% 7.05/2.44  tff(c_4081, plain, ('#skF_3'('#skF_8', k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_4045, c_2424])).
% 7.05/2.44  tff(c_26, plain, (![A_18, B_19]: (r2_hidden('#skF_3'(A_18, B_19), A_18) | r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.05/2.44  tff(c_4098, plain, (r2_hidden('#skF_7', '#skF_8') | r1_xboole_0('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4081, c_26])).
% 7.05/2.44  tff(c_4104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2424, c_566, c_4098])).
% 7.05/2.44  tff(c_4105, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2385])).
% 7.05/2.44  tff(c_354, plain, (![A_123, B_124]: (r2_hidden('#skF_3'(A_123, B_124), A_123) | r1_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.05/2.44  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.05/2.44  tff(c_364, plain, (![A_125, B_126]: (~v1_xboole_0(A_125) | r1_xboole_0(A_125, B_126))), inference(resolution, [status(thm)], [c_354, c_4])).
% 7.05/2.44  tff(c_44, plain, (![A_34]: (~r1_xboole_0(A_34, A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.05/2.44  tff(c_373, plain, (![B_126]: (k1_xboole_0=B_126 | ~v1_xboole_0(B_126))), inference(resolution, [status(thm)], [c_364, c_44])).
% 7.05/2.44  tff(c_4121, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_4105, c_373])).
% 7.05/2.44  tff(c_4131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_4121])).
% 7.05/2.44  tff(c_4132, plain, (k1_tarski('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_88])).
% 7.05/2.44  tff(c_4133, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_88])).
% 7.05/2.44  tff(c_42, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.05/2.44  tff(c_4135, plain, (r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4133, c_4133, c_42])).
% 7.05/2.44  tff(c_4388, plain, (![A_398, B_399, C_400]: (~r1_xboole_0(A_398, B_399) | ~r2_hidden(C_400, k3_xboole_0(A_398, B_399)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_4434, plain, (![A_403, C_404]: (~r1_xboole_0(A_403, A_403) | ~r2_hidden(C_404, A_403))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4388])).
% 7.05/2.44  tff(c_4443, plain, (![C_405]: (~r2_hidden(C_405, '#skF_8'))), inference(resolution, [status(thm)], [c_4135, c_4434])).
% 7.05/2.44  tff(c_4453, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_6, c_4443])).
% 7.05/2.44  tff(c_4367, plain, (![A_392, B_393]: (r2_hidden('#skF_2'(A_392, B_393), A_392) | r1_tarski(A_392, B_393))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.44  tff(c_4377, plain, (![A_394, B_395]: (~v1_xboole_0(A_394) | r1_tarski(A_394, B_395))), inference(resolution, [status(thm)], [c_4367, c_4])).
% 7.05/2.44  tff(c_38, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.05/2.44  tff(c_4386, plain, (![A_394, B_395]: (k2_xboole_0(A_394, B_395)=B_395 | ~v1_xboole_0(A_394))), inference(resolution, [status(thm)], [c_4377, c_38])).
% 7.05/2.44  tff(c_4456, plain, (![B_395]: (k2_xboole_0('#skF_8', B_395)=B_395)), inference(resolution, [status(thm)], [c_4453, c_4386])).
% 7.05/2.44  tff(c_4474, plain, (k1_tarski('#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4456, c_92])).
% 7.05/2.44  tff(c_4476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4132, c_4474])).
% 7.05/2.44  tff(c_4477, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_86])).
% 7.05/2.44  tff(c_6253, plain, (![A_559, B_560]: (k5_xboole_0(k5_xboole_0(A_559, B_560), k2_xboole_0(A_559, B_560))=k3_xboole_0(A_559, B_560))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_6295, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, A_14), A_14)=k3_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6253])).
% 7.05/2.44  tff(c_6303, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20, c_6295])).
% 7.05/2.44  tff(c_6861, plain, (![A_576, B_577, C_578]: (k5_xboole_0(k5_xboole_0(A_576, B_577), C_578)=k5_xboole_0(A_576, k5_xboole_0(B_577, C_578)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.05/2.44  tff(c_6950, plain, (![A_40, C_578]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_578))=k5_xboole_0(k1_xboole_0, C_578))), inference(superposition, [status(thm), theory('equality')], [c_50, c_6861])).
% 7.05/2.44  tff(c_6967, plain, (![A_40, C_578]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_578))=C_578)), inference(demodulation, [status(thm), theory('equality')], [c_6303, c_6950])).
% 7.05/2.44  tff(c_4478, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_86])).
% 7.05/2.44  tff(c_4483, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_92])).
% 7.05/2.44  tff(c_6292, plain, (k5_xboole_0(k5_xboole_0('#skF_8', '#skF_9'), '#skF_8')=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4483, c_6253])).
% 7.05/2.44  tff(c_6407, plain, (k5_xboole_0('#skF_8', k5_xboole_0('#skF_8', '#skF_9'))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2, c_6292])).
% 7.05/2.44  tff(c_6982, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6967, c_6407])).
% 7.05/2.44  tff(c_4841, plain, (![A_453, B_454, C_455]: (~r1_xboole_0(A_453, B_454) | ~r2_hidden(C_455, k3_xboole_0(A_453, B_454)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_4854, plain, (![A_453, B_454]: (~r1_xboole_0(A_453, B_454) | v1_xboole_0(k3_xboole_0(A_453, B_454)))), inference(resolution, [status(thm)], [c_6, c_4841])).
% 7.05/2.44  tff(c_7074, plain, (~r1_xboole_0('#skF_8', '#skF_9') | v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6982, c_4854])).
% 7.05/2.44  tff(c_7422, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_7074])).
% 7.05/2.44  tff(c_90, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.05/2.44  tff(c_4525, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4478, c_4478, c_90])).
% 7.05/2.44  tff(c_40, plain, (![A_32, B_33]: (r1_tarski(k3_xboole_0(A_32, B_33), A_32))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.05/2.44  tff(c_7092, plain, (r1_tarski('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_6982, c_40])).
% 7.05/2.44  tff(c_32, plain, (![B_29, A_28]: (B_29=A_28 | ~r1_tarski(B_29, A_28) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.05/2.44  tff(c_7157, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_7092, c_32])).
% 7.05/2.44  tff(c_7169, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_4525, c_7157])).
% 7.05/2.44  tff(c_5392, plain, (![A_499, B_500]: (r2_hidden('#skF_2'(A_499, B_500), A_499) | r1_tarski(A_499, B_500))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.44  tff(c_4536, plain, (![C_418, A_419]: (C_418=A_419 | ~r2_hidden(C_418, k1_tarski(A_419)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.44  tff(c_4543, plain, (![C_418]: (C_418='#skF_7' | ~r2_hidden(C_418, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4478, c_4536])).
% 7.05/2.44  tff(c_5425, plain, (![B_500]: ('#skF_2'('#skF_8', B_500)='#skF_7' | r1_tarski('#skF_8', B_500))), inference(resolution, [status(thm)], [c_5392, c_4543])).
% 7.05/2.44  tff(c_7180, plain, ('#skF_2'('#skF_8', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_5425, c_7169])).
% 7.05/2.44  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.44  tff(c_7402, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7180, c_10])).
% 7.05/2.44  tff(c_7410, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_7169, c_7402])).
% 7.05/2.44  tff(c_4908, plain, (![A_464, B_465]: (r2_hidden('#skF_3'(A_464, B_465), A_464) | r1_xboole_0(A_464, B_465))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.05/2.44  tff(c_4934, plain, (![B_465]: ('#skF_3'('#skF_8', B_465)='#skF_7' | r1_xboole_0('#skF_8', B_465))), inference(resolution, [status(thm)], [c_4908, c_4543])).
% 7.05/2.44  tff(c_7443, plain, ('#skF_3'('#skF_8', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_4934, c_7422])).
% 7.05/2.44  tff(c_24, plain, (![A_18, B_19]: (r2_hidden('#skF_3'(A_18, B_19), B_19) | r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.05/2.44  tff(c_7455, plain, (r2_hidden('#skF_7', '#skF_9') | r1_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7443, c_24])).
% 7.05/2.44  tff(c_7462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7422, c_7410, c_7455])).
% 7.05/2.44  tff(c_7463, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_7074])).
% 7.05/2.44  tff(c_5026, plain, (![A_471, B_472]: (~v1_xboole_0(A_471) | r1_xboole_0(A_471, B_472))), inference(resolution, [status(thm)], [c_4908, c_4])).
% 7.05/2.44  tff(c_5039, plain, (![B_472]: (k1_xboole_0=B_472 | ~v1_xboole_0(B_472))), inference(resolution, [status(thm)], [c_5026, c_44])).
% 7.05/2.44  tff(c_7482, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_7463, c_5039])).
% 7.05/2.44  tff(c_7494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4477, c_7482])).
% 7.05/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.44  
% 7.05/2.44  Inference rules
% 7.05/2.44  ----------------------
% 7.05/2.44  #Ref     : 2
% 7.05/2.44  #Sup     : 1821
% 7.05/2.44  #Fact    : 0
% 7.05/2.44  #Define  : 0
% 7.05/2.44  #Split   : 7
% 7.05/2.44  #Chain   : 0
% 7.05/2.44  #Close   : 0
% 7.05/2.44  
% 7.05/2.44  Ordering : KBO
% 7.05/2.44  
% 7.05/2.44  Simplification rules
% 7.05/2.44  ----------------------
% 7.05/2.44  #Subsume      : 580
% 7.05/2.44  #Demod        : 526
% 7.05/2.44  #Tautology    : 724
% 7.05/2.44  #SimpNegUnit  : 82
% 7.05/2.44  #BackRed      : 8
% 7.05/2.44  
% 7.05/2.44  #Partial instantiations: 0
% 7.05/2.44  #Strategies tried      : 1
% 7.05/2.44  
% 7.05/2.44  Timing (in seconds)
% 7.05/2.44  ----------------------
% 7.05/2.44  Preprocessing        : 0.37
% 7.05/2.44  Parsing              : 0.19
% 7.05/2.44  CNF conversion       : 0.03
% 7.05/2.44  Main loop            : 1.28
% 7.05/2.44  Inferencing          : 0.41
% 7.05/2.44  Reduction            : 0.47
% 7.05/2.44  Demodulation         : 0.34
% 7.05/2.44  BG Simplification    : 0.05
% 7.05/2.44  Subsumption          : 0.24
% 7.05/2.44  Abstraction          : 0.06
% 7.05/2.44  MUC search           : 0.00
% 7.05/2.44  Cooper               : 0.00
% 7.05/2.44  Total                : 1.70
% 7.05/2.44  Index Insertion      : 0.00
% 7.05/2.44  Index Deletion       : 0.00
% 7.05/2.44  Index Matching       : 0.00
% 7.05/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

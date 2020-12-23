%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:07 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 142 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 197 expanded)
%              Number of equality atoms :   75 ( 120 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_87,axiom,(
    ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

tff(f_89,axiom,(
    ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_34,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2213,plain,(
    ! [A_173,B_174,C_175] : k6_enumset1(A_173,A_173,A_173,A_173,A_173,A_173,B_174,C_175) = k1_enumset1(A_173,B_174,C_175) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    ! [A_39] : k6_enumset1(A_39,A_39,A_39,A_39,A_39,A_39,A_39,A_39) = k1_tarski(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2220,plain,(
    ! [C_175] : k1_enumset1(C_175,C_175,C_175) = k1_tarski(C_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_52])).

tff(c_1527,plain,(
    ! [A_138,B_139,C_140,D_141] : k2_xboole_0(k2_tarski(A_138,B_139),k2_tarski(C_140,D_141)) = k2_enumset1(A_138,B_139,C_140,D_141) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1553,plain,(
    ! [C_142,D_143] : k2_enumset1(C_142,D_143,C_142,D_143) = k2_tarski(C_142,D_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_6])).

tff(c_48,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1560,plain,(
    ! [D_143] : k1_enumset1(D_143,D_143,D_143) = k2_tarski(D_143,D_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_1553,c_48])).

tff(c_2243,plain,(
    ! [D_177] : k2_tarski(D_177,D_177) = k1_tarski(D_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2220,c_1560])).

tff(c_14,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_773,plain,(
    ! [A_98,C_99,B_100] :
      ( ~ r2_hidden(A_98,C_99)
      | k4_xboole_0(k2_tarski(A_98,B_100),C_99) != k1_tarski(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_785,plain,(
    ! [A_98,B_100] :
      ( ~ r2_hidden(A_98,k2_tarski(A_98,B_100))
      | k1_tarski(A_98) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_773])).

tff(c_2264,plain,(
    ! [D_177] :
      ( ~ r2_hidden(D_177,k1_tarski(D_177))
      | k1_tarski(D_177) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2243,c_785])).

tff(c_2277,plain,(
    ! [D_177] : k1_tarski(D_177) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2264])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_160,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_149])).

tff(c_64,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_62,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_xboole_0(k2_tarski(A_26,B_27),k2_tarski(C_28,D_29)) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2255,plain,(
    ! [D_177,C_28,D_29] : k2_xboole_0(k1_tarski(D_177),k2_tarski(C_28,D_29)) = k2_enumset1(D_177,D_177,C_28,D_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_2243,c_44])).

tff(c_5566,plain,(
    ! [D_281,C_282,D_283] : k2_xboole_0(k1_tarski(D_281),k2_tarski(C_282,D_283)) = k1_enumset1(D_281,C_282,D_283) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2255])).

tff(c_18,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(C_11,'#skF_1'(A_9,B_10,C_11))
      | k2_xboole_0(A_9,C_11) = B_10
      | ~ r1_tarski(C_11,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2581,plain,(
    ! [B_197,A_198,C_199] :
      ( ~ r1_tarski(B_197,'#skF_1'(A_198,B_197,C_199))
      | k2_xboole_0(A_198,C_199) = B_197
      | ~ r1_tarski(C_199,B_197)
      | ~ r1_tarski(A_198,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2585,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(B_10,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_2581])).

tff(c_2594,plain,(
    ! [A_200,B_201] :
      ( k2_xboole_0(A_200,B_201) = B_201
      | ~ r1_tarski(A_200,B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2585])).

tff(c_2609,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_2594])).

tff(c_5578,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_6') = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5566,c_2609])).

tff(c_46,plain,(
    ! [A_30,B_31,C_32] :
      ( k4_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(A_30)) = k2_tarski(B_31,C_32)
      | C_32 = A_30
      | B_31 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5623,plain,
    ( k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_4')) = k2_tarski('#skF_5','#skF_6')
    | '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5578,c_46])).

tff(c_5629,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_4')) = k2_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_5623])).

tff(c_28,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_67,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_81,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,A_49)
      | ~ r1_xboole_0(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_67,c_81])).

tff(c_117,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [B_20,A_19] : k3_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_117])).

tff(c_283,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_310,plain,(
    ! [B_20,A_19] : k4_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k4_xboole_0(B_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_283])).

tff(c_5801,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k4_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5629,c_310])).

tff(c_5842,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_5801])).

tff(c_162,plain,(
    ! [B_69] : k4_xboole_0(B_69,B_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_125,plain,(
    ! [A_19,B_20] : k3_xboole_0(k4_xboole_0(A_19,B_20),B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_117])).

tff(c_170,plain,(
    ! [B_69] : k3_xboole_0(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_125])).

tff(c_307,plain,(
    ! [B_69] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_283])).

tff(c_323,plain,(
    ! [B_69] : k4_xboole_0(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_307])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_416,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1409,plain,(
    ! [B_132,A_133] :
      ( B_132 = A_133
      | ~ r1_tarski(B_132,A_133)
      | k4_xboole_0(A_133,B_132) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_416])).

tff(c_2158,plain,(
    ! [B_168,A_169] :
      ( B_168 = A_169
      | k4_xboole_0(B_168,A_169) != k1_xboole_0
      | k4_xboole_0(A_169,B_168) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_1409])).

tff(c_2176,plain,(
    ! [B_69] :
      ( k1_xboole_0 = B_69
      | k4_xboole_0(B_69,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_2158])).

tff(c_5914,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5842,c_2176])).

tff(c_6027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2277,c_5914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.03  
% 5.36/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.36/2.04  
% 5.36/2.04  %Foreground sorts:
% 5.36/2.04  
% 5.36/2.04  
% 5.36/2.04  %Background operators:
% 5.36/2.04  
% 5.36/2.04  
% 5.36/2.04  %Foreground operators:
% 5.36/2.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.36/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.36/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.36/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.36/2.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.36/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.36/2.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.36/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.36/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.36/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.36/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.36/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.36/2.04  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.36/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.36/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.36/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.36/2.04  
% 5.36/2.05  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.36/2.05  tff(f_87, axiom, (![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 5.36/2.05  tff(f_89, axiom, (![A]: (k6_enumset1(A, A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_enumset1)).
% 5.36/2.05  tff(f_73, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 5.36/2.05  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.36/2.05  tff(f_85, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.36/2.05  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.36/2.05  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.36/2.05  tff(f_98, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 5.36/2.05  tff(f_108, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 5.36/2.05  tff(f_54, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 5.36/2.05  tff(f_83, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 5.36/2.05  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.36/2.05  tff(f_64, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 5.36/2.05  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.36/2.05  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.36/2.05  tff(c_34, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.36/2.05  tff(c_2213, plain, (![A_173, B_174, C_175]: (k6_enumset1(A_173, A_173, A_173, A_173, A_173, A_173, B_174, C_175)=k1_enumset1(A_173, B_174, C_175))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.36/2.05  tff(c_52, plain, (![A_39]: (k6_enumset1(A_39, A_39, A_39, A_39, A_39, A_39, A_39, A_39)=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.36/2.05  tff(c_2220, plain, (![C_175]: (k1_enumset1(C_175, C_175, C_175)=k1_tarski(C_175))), inference(superposition, [status(thm), theory('equality')], [c_2213, c_52])).
% 5.36/2.05  tff(c_1527, plain, (![A_138, B_139, C_140, D_141]: (k2_xboole_0(k2_tarski(A_138, B_139), k2_tarski(C_140, D_141))=k2_enumset1(A_138, B_139, C_140, D_141))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.36/2.05  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.36/2.05  tff(c_1553, plain, (![C_142, D_143]: (k2_enumset1(C_142, D_143, C_142, D_143)=k2_tarski(C_142, D_143))), inference(superposition, [status(thm), theory('equality')], [c_1527, c_6])).
% 5.36/2.05  tff(c_48, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.36/2.05  tff(c_1560, plain, (![D_143]: (k1_enumset1(D_143, D_143, D_143)=k2_tarski(D_143, D_143))), inference(superposition, [status(thm), theory('equality')], [c_1553, c_48])).
% 5.36/2.05  tff(c_2243, plain, (![D_177]: (k2_tarski(D_177, D_177)=k1_tarski(D_177))), inference(demodulation, [status(thm), theory('equality')], [c_2220, c_1560])).
% 5.36/2.05  tff(c_14, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.36/2.05  tff(c_149, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.36/2.05  tff(c_161, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_149])).
% 5.36/2.05  tff(c_773, plain, (![A_98, C_99, B_100]: (~r2_hidden(A_98, C_99) | k4_xboole_0(k2_tarski(A_98, B_100), C_99)!=k1_tarski(A_98))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.36/2.05  tff(c_785, plain, (![A_98, B_100]: (~r2_hidden(A_98, k2_tarski(A_98, B_100)) | k1_tarski(A_98)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_161, c_773])).
% 5.36/2.05  tff(c_2264, plain, (![D_177]: (~r2_hidden(D_177, k1_tarski(D_177)) | k1_tarski(D_177)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2243, c_785])).
% 5.36/2.05  tff(c_2277, plain, (![D_177]: (k1_tarski(D_177)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2264])).
% 5.36/2.05  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.36/2.05  tff(c_160, plain, (k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_149])).
% 5.36/2.05  tff(c_64, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.36/2.05  tff(c_62, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.36/2.05  tff(c_44, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k2_tarski(A_26, B_27), k2_tarski(C_28, D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.36/2.05  tff(c_2255, plain, (![D_177, C_28, D_29]: (k2_xboole_0(k1_tarski(D_177), k2_tarski(C_28, D_29))=k2_enumset1(D_177, D_177, C_28, D_29))), inference(superposition, [status(thm), theory('equality')], [c_2243, c_44])).
% 5.36/2.05  tff(c_5566, plain, (![D_281, C_282, D_283]: (k2_xboole_0(k1_tarski(D_281), k2_tarski(C_282, D_283))=k1_enumset1(D_281, C_282, D_283))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2255])).
% 5.36/2.05  tff(c_18, plain, (![C_11, A_9, B_10]: (r1_tarski(C_11, '#skF_1'(A_9, B_10, C_11)) | k2_xboole_0(A_9, C_11)=B_10 | ~r1_tarski(C_11, B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.05  tff(c_2581, plain, (![B_197, A_198, C_199]: (~r1_tarski(B_197, '#skF_1'(A_198, B_197, C_199)) | k2_xboole_0(A_198, C_199)=B_197 | ~r1_tarski(C_199, B_197) | ~r1_tarski(A_198, B_197))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.05  tff(c_2585, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(B_10, B_10) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_18, c_2581])).
% 5.36/2.05  tff(c_2594, plain, (![A_200, B_201]: (k2_xboole_0(A_200, B_201)=B_201 | ~r1_tarski(A_200, B_201))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2585])).
% 5.36/2.05  tff(c_2609, plain, (k2_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_2594])).
% 5.36/2.05  tff(c_5578, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_6')=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5566, c_2609])).
% 5.36/2.05  tff(c_46, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(A_30))=k2_tarski(B_31, C_32) | C_32=A_30 | B_31=A_30)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.36/2.05  tff(c_5623, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_4'))=k2_tarski('#skF_5', '#skF_6') | '#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5578, c_46])).
% 5.36/2.05  tff(c_5629, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_4'))=k2_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_5623])).
% 5.36/2.05  tff(c_28, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.36/2.05  tff(c_30, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, k3_xboole_0(A_19, B_20)), B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.36/2.05  tff(c_67, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 5.36/2.05  tff(c_81, plain, (![B_48, A_49]: (r1_xboole_0(B_48, A_49) | ~r1_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.36/2.05  tff(c_84, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_67, c_81])).
% 5.36/2.05  tff(c_117, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.36/2.05  tff(c_124, plain, (![B_20, A_19]: (k3_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_117])).
% 5.36/2.05  tff(c_283, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.36/2.05  tff(c_310, plain, (![B_20, A_19]: (k4_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k4_xboole_0(B_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_283])).
% 5.36/2.05  tff(c_5801, plain, (k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k4_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5629, c_310])).
% 5.36/2.05  tff(c_5842, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_160, c_5801])).
% 5.36/2.05  tff(c_162, plain, (![B_69]: (k4_xboole_0(B_69, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_149])).
% 5.36/2.05  tff(c_125, plain, (![A_19, B_20]: (k3_xboole_0(k4_xboole_0(A_19, B_20), B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_67, c_117])).
% 5.36/2.05  tff(c_170, plain, (![B_69]: (k3_xboole_0(k1_xboole_0, B_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_162, c_125])).
% 5.36/2.05  tff(c_307, plain, (![B_69]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_69))), inference(superposition, [status(thm), theory('equality')], [c_170, c_283])).
% 5.36/2.05  tff(c_323, plain, (![B_69]: (k4_xboole_0(k1_xboole_0, B_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_307])).
% 5.36/2.05  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.36/2.05  tff(c_416, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.36/2.05  tff(c_1409, plain, (![B_132, A_133]: (B_132=A_133 | ~r1_tarski(B_132, A_133) | k4_xboole_0(A_133, B_132)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_416])).
% 5.36/2.05  tff(c_2158, plain, (![B_168, A_169]: (B_168=A_169 | k4_xboole_0(B_168, A_169)!=k1_xboole_0 | k4_xboole_0(A_169, B_168)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_1409])).
% 5.36/2.05  tff(c_2176, plain, (![B_69]: (k1_xboole_0=B_69 | k4_xboole_0(B_69, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_323, c_2158])).
% 5.36/2.05  tff(c_5914, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5842, c_2176])).
% 5.36/2.05  tff(c_6027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2277, c_5914])).
% 5.36/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.05  
% 5.36/2.05  Inference rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Ref     : 0
% 5.36/2.05  #Sup     : 1524
% 5.36/2.05  #Fact    : 0
% 5.36/2.05  #Define  : 0
% 5.36/2.05  #Split   : 2
% 5.36/2.05  #Chain   : 0
% 5.36/2.05  #Close   : 0
% 5.36/2.05  
% 5.36/2.05  Ordering : KBO
% 5.36/2.05  
% 5.36/2.05  Simplification rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Subsume      : 73
% 5.36/2.05  #Demod        : 1221
% 5.36/2.05  #Tautology    : 951
% 5.36/2.05  #SimpNegUnit  : 29
% 5.36/2.05  #BackRed      : 6
% 5.36/2.05  
% 5.36/2.05  #Partial instantiations: 0
% 5.36/2.05  #Strategies tried      : 1
% 5.36/2.05  
% 5.36/2.05  Timing (in seconds)
% 5.36/2.05  ----------------------
% 5.36/2.06  Preprocessing        : 0.33
% 5.36/2.06  Parsing              : 0.17
% 5.36/2.06  CNF conversion       : 0.02
% 5.36/2.06  Main loop            : 0.92
% 5.36/2.06  Inferencing          : 0.28
% 5.36/2.06  Reduction            : 0.38
% 5.36/2.06  Demodulation         : 0.29
% 5.36/2.06  BG Simplification    : 0.04
% 5.36/2.06  Subsumption          : 0.17
% 5.36/2.06  Abstraction          : 0.04
% 5.36/2.06  MUC search           : 0.00
% 5.36/2.06  Cooper               : 0.00
% 5.36/2.06  Total                : 1.29
% 5.36/2.06  Index Insertion      : 0.00
% 5.36/2.06  Index Deletion       : 0.00
% 5.36/2.06  Index Matching       : 0.00
% 5.36/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------

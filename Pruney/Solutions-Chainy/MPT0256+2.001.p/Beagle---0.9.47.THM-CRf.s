%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:02 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 511 expanded)
%              Number of leaves         :   36 ( 177 expanded)
%              Depth                    :   20
%              Number of atoms          :  150 (1026 expanded)
%              Number of equality atoms :   51 ( 221 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_79,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_103,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_58,plain,(
    ! [D_46,A_41] : r2_hidden(D_46,k2_tarski(A_41,D_46)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_210,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,k3_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_224,plain,(
    ! [A_30,C_79] :
      ( ~ r1_xboole_0(A_30,k1_xboole_0)
      | ~ r2_hidden(C_79,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_210])).

tff(c_228,plain,(
    ! [C_80] : ~ r2_hidden(C_80,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_238,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_54,plain,(
    ! [A_40] : k5_xboole_0(A_40,A_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_251,plain,(
    ! [A_82] : r1_xboole_0(A_82,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_50,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = A_38
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_264,plain,(
    ! [A_82] : k4_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(resolution,[status(thm)],[c_251,c_50])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_237,plain,(
    ! [B_12] : r1_xboole_0(k1_xboole_0,B_12) ),
    inference(resolution,[status(thm)],[c_28,c_228])).

tff(c_329,plain,(
    ! [A_88,B_89,B_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | r1_xboole_0(k3_xboole_0(A_88,B_89),B_90) ) ),
    inference(resolution,[status(thm)],[c_28,c_210])).

tff(c_46,plain,(
    ! [A_34] :
      ( ~ r1_xboole_0(A_34,A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_350,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = k1_xboole_0
      | ~ r1_xboole_0(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_329,c_46])).

tff(c_366,plain,(
    ! [B_12] : k3_xboole_0(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_237,c_350])).

tff(c_3090,plain,(
    ! [A_202,B_203,C_204] : k2_xboole_0(k4_xboole_0(A_202,B_203),k4_xboole_0(A_202,C_204)) = k4_xboole_0(A_202,k3_xboole_0(B_203,C_204)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3143,plain,(
    ! [A_82,C_204] : k4_xboole_0(A_82,k3_xboole_0(k1_xboole_0,C_204)) = k2_xboole_0(A_82,k4_xboole_0(A_82,C_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_3090])).

tff(c_3297,plain,(
    ! [A_206,C_207] : k2_xboole_0(A_206,k4_xboole_0(A_206,C_207)) = A_206 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_366,c_3143])).

tff(c_3436,plain,(
    ! [A_209] : k2_xboole_0(A_209,A_209) = A_209 ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_3297])).

tff(c_22,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),k4_xboole_0(B_10,A_9)) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3447,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_3436,c_22])).

tff(c_3529,plain,(
    ! [A_212] : k4_xboole_0(A_212,A_212) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3447])).

tff(c_48,plain,(
    ! [B_36,A_35,C_37] :
      ( r1_xboole_0(B_36,k4_xboole_0(A_35,C_37))
      | ~ r1_xboole_0(A_35,k4_xboole_0(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3570,plain,(
    ! [A_212,A_35] :
      ( r1_xboole_0(A_212,k4_xboole_0(A_35,A_212))
      | ~ r1_xboole_0(A_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3529,c_48])).

tff(c_3836,plain,(
    ! [A_219,A_220] : r1_xboole_0(A_219,k4_xboole_0(A_220,A_219)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_3570])).

tff(c_76,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden(A_48,B_49)
      | ~ r1_xboole_0(k1_tarski(A_48),B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4853,plain,(
    ! [A_248,A_249] : ~ r2_hidden(A_248,k4_xboole_0(A_249,k1_tarski(A_248))) ),
    inference(resolution,[status(thm)],[c_3836,c_76])).

tff(c_6440,plain,(
    ! [D_290,A_291] :
      ( r2_hidden(D_290,k1_tarski(D_290))
      | ~ r2_hidden(D_290,A_291) ) ),
    inference(resolution,[status(thm)],[c_4,c_4853])).

tff(c_6469,plain,(
    ! [D_46] : r2_hidden(D_46,k1_tarski(D_46)) ),
    inference(resolution,[status(thm)],[c_58,c_6440])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_227,plain,(
    ! [C_79] : ~ r2_hidden(C_79,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_3460,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3447])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_964,plain,(
    ! [B_122,A_123,C_124] :
      ( r1_xboole_0(B_122,k4_xboole_0(A_123,C_124))
      | ~ r1_xboole_0(A_123,k4_xboole_0(B_122,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_971,plain,(
    ! [A_82,A_123] :
      ( r1_xboole_0(A_82,k4_xboole_0(A_123,k1_xboole_0))
      | ~ r1_xboole_0(A_123,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_964])).

tff(c_987,plain,(
    ! [A_125,A_126] :
      ( r1_xboole_0(A_125,A_126)
      | ~ r1_xboole_0(A_126,A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_971])).

tff(c_1004,plain,(
    ! [B_39,A_38] :
      ( r1_xboole_0(B_39,A_38)
      | k4_xboole_0(A_38,B_39) != A_38 ) ),
    inference(resolution,[status(thm)],[c_52,c_987])).

tff(c_38,plain,(
    ! [A_27,B_28,C_29] : k3_xboole_0(k3_xboole_0(A_27,B_28),C_29) = k3_xboole_0(A_27,k3_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_225,plain,(
    ! [A_77,B_78,B_12] :
      ( ~ r1_xboole_0(A_77,B_78)
      | r1_xboole_0(k3_xboole_0(A_77,B_78),B_12) ) ),
    inference(resolution,[status(thm)],[c_28,c_210])).

tff(c_363,plain,(
    ! [A_77,B_78,B_12] :
      ( k3_xboole_0(k3_xboole_0(A_77,B_78),B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_225,c_350])).

tff(c_785,plain,(
    ! [A_77,B_78,B_12] :
      ( k3_xboole_0(A_77,k3_xboole_0(B_78,B_12)) = k1_xboole_0
      | ~ r1_xboole_0(A_77,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_363])).

tff(c_1192,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_4'(A_137,B_138),k3_xboole_0(A_137,B_138))
      | r1_xboole_0(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1204,plain,(
    ! [A_77,B_78,B_12] :
      ( r2_hidden('#skF_4'(A_77,k3_xboole_0(B_78,B_12)),k1_xboole_0)
      | r1_xboole_0(A_77,k3_xboole_0(B_78,B_12))
      | ~ r1_xboole_0(A_77,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_1192])).

tff(c_1448,plain,(
    ! [A_153,B_154,B_155] :
      ( r1_xboole_0(A_153,k3_xboole_0(B_154,B_155))
      | ~ r1_xboole_0(A_153,B_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_1204])).

tff(c_981,plain,(
    ! [A_82,A_123] :
      ( r1_xboole_0(A_82,A_123)
      | ~ r1_xboole_0(A_123,A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_971])).

tff(c_1498,plain,(
    ! [B_154,B_155,A_153] :
      ( r1_xboole_0(k3_xboole_0(B_154,B_155),A_153)
      | ~ r1_xboole_0(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_1448,c_981])).

tff(c_1842,plain,(
    ! [B_167,B_168] :
      ( k3_xboole_0(B_167,B_168) = k1_xboole_0
      | ~ r1_xboole_0(k3_xboole_0(B_167,B_168),B_167) ) ),
    inference(resolution,[status(thm)],[c_1448,c_46])).

tff(c_2037,plain,(
    ! [A_172,B_173] :
      ( k3_xboole_0(A_172,B_173) = k1_xboole_0
      | ~ r1_xboole_0(A_172,A_172) ) ),
    inference(resolution,[status(thm)],[c_1498,c_1842])).

tff(c_2084,plain,(
    ! [A_38,B_173] :
      ( k3_xboole_0(A_38,B_173) = k1_xboole_0
      | k4_xboole_0(A_38,A_38) != A_38 ) ),
    inference(resolution,[status(thm)],[c_1004,c_2037])).

tff(c_4048,plain,(
    ! [A_228,B_229] :
      ( k3_xboole_0(A_228,B_229) = k1_xboole_0
      | k1_xboole_0 != A_228 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3460,c_2084])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),k3_xboole_0(A_16,B_17))
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4129,plain,(
    ! [A_228,B_229] :
      ( r2_hidden('#skF_4'(A_228,B_229),k1_xboole_0)
      | r1_xboole_0(A_228,B_229)
      | k1_xboole_0 != A_228 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4048,c_30])).

tff(c_4268,plain,(
    ! [A_230,B_231] :
      ( r1_xboole_0(A_230,B_231)
      | k1_xboole_0 != A_230 ) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_4129])).

tff(c_4346,plain,(
    ! [B_231] : r1_xboole_0(B_231,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4268,c_981])).

tff(c_347,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(A_88,B_89) = k1_xboole_0
      | ~ r1_xboole_0(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_329,c_46])).

tff(c_3893,plain,(
    ! [A_219,A_220] : k3_xboole_0(A_219,k4_xboole_0(A_220,A_219)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3836,c_347])).

tff(c_34,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k4_xboole_0(A_21,B_22),k4_xboole_0(A_21,C_23)) = k4_xboole_0(A_21,k3_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9301,plain,(
    ! [A_351,B_352] : k4_xboole_0(A_351,k3_xboole_0(B_352,B_352)) = k4_xboole_0(A_351,B_352) ),
    inference(superposition,[status(thm),theory(equality)],[c_3436,c_34])).

tff(c_80,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2575,plain,(
    ! [A_188,B_189,C_190] : k4_xboole_0(k3_xboole_0(A_188,B_189),k3_xboole_0(A_188,C_190)) = k3_xboole_0(A_188,k4_xboole_0(B_189,C_190)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2684,plain,(
    ! [C_190] : k4_xboole_0(k1_tarski('#skF_8'),k3_xboole_0('#skF_7',C_190)) = k3_xboole_0('#skF_7',k4_xboole_0(k1_tarski('#skF_8'),C_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_2575])).

tff(c_9360,plain,(
    k3_xboole_0('#skF_7',k4_xboole_0(k1_tarski('#skF_8'),'#skF_7')) = k4_xboole_0(k1_tarski('#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_9301,c_2684])).

tff(c_9501,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3893,c_9360])).

tff(c_9586,plain,(
    ! [A_35] :
      ( r1_xboole_0(k1_tarski('#skF_8'),k4_xboole_0(A_35,'#skF_7'))
      | ~ r1_xboole_0(A_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9501,c_48])).

tff(c_10829,plain,(
    ! [A_366] : r1_xboole_0(k1_tarski('#skF_8'),k4_xboole_0(A_366,'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4346,c_9586])).

tff(c_10889,plain,(
    ! [A_367] : ~ r2_hidden('#skF_8',k4_xboole_0(A_367,'#skF_7')) ),
    inference(resolution,[status(thm)],[c_10829,c_76])).

tff(c_10917,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_8','#skF_7')
      | ~ r2_hidden('#skF_8',A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_10889])).

tff(c_10924,plain,(
    ! [A_368] : ~ r2_hidden('#skF_8',A_368) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_10917])).

tff(c_10944,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6469,c_10924])).

tff(c_10945,plain,(
    ! [A_30] : ~ r1_xboole_0(A_30,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_44,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10945,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.64  
% 7.11/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.64  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4
% 7.11/2.64  
% 7.11/2.64  %Foreground sorts:
% 7.11/2.64  
% 7.11/2.64  
% 7.11/2.64  %Background operators:
% 7.11/2.64  
% 7.11/2.64  
% 7.11/2.64  %Foreground operators:
% 7.11/2.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.11/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.11/2.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.11/2.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.11/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.64  tff('#skF_7', type, '#skF_7': $i).
% 7.11/2.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.11/2.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.11/2.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.11/2.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.11/2.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.11/2.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.11/2.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.64  tff('#skF_8', type, '#skF_8': $i).
% 7.11/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.11/2.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.11/2.64  
% 7.16/2.66  tff(f_112, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.16/2.66  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.16/2.66  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.16/2.66  tff(f_79, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.16/2.66  tff(f_71, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.16/2.66  tff(f_103, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.16/2.66  tff(f_101, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.16/2.66  tff(f_93, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 7.16/2.66  tff(f_73, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 7.16/2.66  tff(f_39, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 7.16/2.66  tff(f_97, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 7.16/2.66  tff(f_119, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 7.16/2.66  tff(f_124, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 7.16/2.66  tff(f_77, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.16/2.66  tff(f_81, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 7.16/2.66  tff(c_58, plain, (![D_46, A_41]: (r2_hidden(D_46, k2_tarski(A_41, D_46)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.16/2.66  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.16/2.66  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.16/2.66  tff(c_40, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.16/2.66  tff(c_210, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, k3_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.16/2.66  tff(c_224, plain, (![A_30, C_79]: (~r1_xboole_0(A_30, k1_xboole_0) | ~r2_hidden(C_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_210])).
% 7.16/2.66  tff(c_228, plain, (![C_80]: (~r2_hidden(C_80, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_224])).
% 7.16/2.66  tff(c_238, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_228])).
% 7.16/2.66  tff(c_54, plain, (![A_40]: (k5_xboole_0(A_40, A_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.16/2.66  tff(c_251, plain, (![A_82]: (r1_xboole_0(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_228])).
% 7.16/2.66  tff(c_50, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=A_38 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.16/2.66  tff(c_264, plain, (![A_82]: (k4_xboole_0(A_82, k1_xboole_0)=A_82)), inference(resolution, [status(thm)], [c_251, c_50])).
% 7.16/2.66  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.16/2.66  tff(c_237, plain, (![B_12]: (r1_xboole_0(k1_xboole_0, B_12))), inference(resolution, [status(thm)], [c_28, c_228])).
% 7.16/2.66  tff(c_329, plain, (![A_88, B_89, B_90]: (~r1_xboole_0(A_88, B_89) | r1_xboole_0(k3_xboole_0(A_88, B_89), B_90))), inference(resolution, [status(thm)], [c_28, c_210])).
% 7.16/2.66  tff(c_46, plain, (![A_34]: (~r1_xboole_0(A_34, A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.16/2.66  tff(c_350, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=k1_xboole_0 | ~r1_xboole_0(A_91, B_92))), inference(resolution, [status(thm)], [c_329, c_46])).
% 7.16/2.66  tff(c_366, plain, (![B_12]: (k3_xboole_0(k1_xboole_0, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_350])).
% 7.16/2.66  tff(c_3090, plain, (![A_202, B_203, C_204]: (k2_xboole_0(k4_xboole_0(A_202, B_203), k4_xboole_0(A_202, C_204))=k4_xboole_0(A_202, k3_xboole_0(B_203, C_204)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.16/2.66  tff(c_3143, plain, (![A_82, C_204]: (k4_xboole_0(A_82, k3_xboole_0(k1_xboole_0, C_204))=k2_xboole_0(A_82, k4_xboole_0(A_82, C_204)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_3090])).
% 7.16/2.66  tff(c_3297, plain, (![A_206, C_207]: (k2_xboole_0(A_206, k4_xboole_0(A_206, C_207))=A_206)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_366, c_3143])).
% 7.16/2.66  tff(c_3436, plain, (![A_209]: (k2_xboole_0(A_209, A_209)=A_209)), inference(superposition, [status(thm), theory('equality')], [c_264, c_3297])).
% 7.16/2.66  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k4_xboole_0(B_10, A_9))=k5_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.16/2.66  tff(c_3447, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_3436, c_22])).
% 7.16/2.66  tff(c_3529, plain, (![A_212]: (k4_xboole_0(A_212, A_212)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3447])).
% 7.16/2.66  tff(c_48, plain, (![B_36, A_35, C_37]: (r1_xboole_0(B_36, k4_xboole_0(A_35, C_37)) | ~r1_xboole_0(A_35, k4_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.16/2.66  tff(c_3570, plain, (![A_212, A_35]: (r1_xboole_0(A_212, k4_xboole_0(A_35, A_212)) | ~r1_xboole_0(A_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3529, c_48])).
% 7.16/2.66  tff(c_3836, plain, (![A_219, A_220]: (r1_xboole_0(A_219, k4_xboole_0(A_220, A_219)))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_3570])).
% 7.16/2.66  tff(c_76, plain, (![A_48, B_49]: (~r2_hidden(A_48, B_49) | ~r1_xboole_0(k1_tarski(A_48), B_49))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.16/2.66  tff(c_4853, plain, (![A_248, A_249]: (~r2_hidden(A_248, k4_xboole_0(A_249, k1_tarski(A_248))))), inference(resolution, [status(thm)], [c_3836, c_76])).
% 7.16/2.66  tff(c_6440, plain, (![D_290, A_291]: (r2_hidden(D_290, k1_tarski(D_290)) | ~r2_hidden(D_290, A_291))), inference(resolution, [status(thm)], [c_4, c_4853])).
% 7.16/2.66  tff(c_6469, plain, (![D_46]: (r2_hidden(D_46, k1_tarski(D_46)))), inference(resolution, [status(thm)], [c_58, c_6440])).
% 7.16/2.66  tff(c_78, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.16/2.66  tff(c_227, plain, (![C_79]: (~r2_hidden(C_79, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_224])).
% 7.16/2.66  tff(c_3460, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3447])).
% 7.16/2.66  tff(c_52, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k4_xboole_0(A_38, B_39)!=A_38)), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.16/2.66  tff(c_964, plain, (![B_122, A_123, C_124]: (r1_xboole_0(B_122, k4_xboole_0(A_123, C_124)) | ~r1_xboole_0(A_123, k4_xboole_0(B_122, C_124)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.16/2.66  tff(c_971, plain, (![A_82, A_123]: (r1_xboole_0(A_82, k4_xboole_0(A_123, k1_xboole_0)) | ~r1_xboole_0(A_123, A_82))), inference(superposition, [status(thm), theory('equality')], [c_264, c_964])).
% 7.16/2.66  tff(c_987, plain, (![A_125, A_126]: (r1_xboole_0(A_125, A_126) | ~r1_xboole_0(A_126, A_125))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_971])).
% 7.16/2.66  tff(c_1004, plain, (![B_39, A_38]: (r1_xboole_0(B_39, A_38) | k4_xboole_0(A_38, B_39)!=A_38)), inference(resolution, [status(thm)], [c_52, c_987])).
% 7.16/2.66  tff(c_38, plain, (![A_27, B_28, C_29]: (k3_xboole_0(k3_xboole_0(A_27, B_28), C_29)=k3_xboole_0(A_27, k3_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.16/2.66  tff(c_225, plain, (![A_77, B_78, B_12]: (~r1_xboole_0(A_77, B_78) | r1_xboole_0(k3_xboole_0(A_77, B_78), B_12))), inference(resolution, [status(thm)], [c_28, c_210])).
% 7.16/2.66  tff(c_363, plain, (![A_77, B_78, B_12]: (k3_xboole_0(k3_xboole_0(A_77, B_78), B_12)=k1_xboole_0 | ~r1_xboole_0(A_77, B_78))), inference(resolution, [status(thm)], [c_225, c_350])).
% 7.16/2.66  tff(c_785, plain, (![A_77, B_78, B_12]: (k3_xboole_0(A_77, k3_xboole_0(B_78, B_12))=k1_xboole_0 | ~r1_xboole_0(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_363])).
% 7.16/2.66  tff(c_1192, plain, (![A_137, B_138]: (r2_hidden('#skF_4'(A_137, B_138), k3_xboole_0(A_137, B_138)) | r1_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.16/2.66  tff(c_1204, plain, (![A_77, B_78, B_12]: (r2_hidden('#skF_4'(A_77, k3_xboole_0(B_78, B_12)), k1_xboole_0) | r1_xboole_0(A_77, k3_xboole_0(B_78, B_12)) | ~r1_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_785, c_1192])).
% 7.16/2.66  tff(c_1448, plain, (![A_153, B_154, B_155]: (r1_xboole_0(A_153, k3_xboole_0(B_154, B_155)) | ~r1_xboole_0(A_153, B_154))), inference(negUnitSimplification, [status(thm)], [c_227, c_1204])).
% 7.16/2.66  tff(c_981, plain, (![A_82, A_123]: (r1_xboole_0(A_82, A_123) | ~r1_xboole_0(A_123, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_971])).
% 7.16/2.66  tff(c_1498, plain, (![B_154, B_155, A_153]: (r1_xboole_0(k3_xboole_0(B_154, B_155), A_153) | ~r1_xboole_0(A_153, B_154))), inference(resolution, [status(thm)], [c_1448, c_981])).
% 7.16/2.66  tff(c_1842, plain, (![B_167, B_168]: (k3_xboole_0(B_167, B_168)=k1_xboole_0 | ~r1_xboole_0(k3_xboole_0(B_167, B_168), B_167))), inference(resolution, [status(thm)], [c_1448, c_46])).
% 7.16/2.66  tff(c_2037, plain, (![A_172, B_173]: (k3_xboole_0(A_172, B_173)=k1_xboole_0 | ~r1_xboole_0(A_172, A_172))), inference(resolution, [status(thm)], [c_1498, c_1842])).
% 7.16/2.66  tff(c_2084, plain, (![A_38, B_173]: (k3_xboole_0(A_38, B_173)=k1_xboole_0 | k4_xboole_0(A_38, A_38)!=A_38)), inference(resolution, [status(thm)], [c_1004, c_2037])).
% 7.16/2.66  tff(c_4048, plain, (![A_228, B_229]: (k3_xboole_0(A_228, B_229)=k1_xboole_0 | k1_xboole_0!=A_228)), inference(demodulation, [status(thm), theory('equality')], [c_3460, c_2084])).
% 7.16/2.66  tff(c_30, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), k3_xboole_0(A_16, B_17)) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.16/2.66  tff(c_4129, plain, (![A_228, B_229]: (r2_hidden('#skF_4'(A_228, B_229), k1_xboole_0) | r1_xboole_0(A_228, B_229) | k1_xboole_0!=A_228)), inference(superposition, [status(thm), theory('equality')], [c_4048, c_30])).
% 7.16/2.66  tff(c_4268, plain, (![A_230, B_231]: (r1_xboole_0(A_230, B_231) | k1_xboole_0!=A_230)), inference(negUnitSimplification, [status(thm)], [c_227, c_4129])).
% 7.16/2.66  tff(c_4346, plain, (![B_231]: (r1_xboole_0(B_231, k1_xboole_0))), inference(resolution, [status(thm)], [c_4268, c_981])).
% 7.16/2.66  tff(c_347, plain, (![A_88, B_89]: (k3_xboole_0(A_88, B_89)=k1_xboole_0 | ~r1_xboole_0(A_88, B_89))), inference(resolution, [status(thm)], [c_329, c_46])).
% 7.16/2.66  tff(c_3893, plain, (![A_219, A_220]: (k3_xboole_0(A_219, k4_xboole_0(A_220, A_219))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3836, c_347])).
% 7.16/2.66  tff(c_34, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k4_xboole_0(A_21, B_22), k4_xboole_0(A_21, C_23))=k4_xboole_0(A_21, k3_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.16/2.66  tff(c_9301, plain, (![A_351, B_352]: (k4_xboole_0(A_351, k3_xboole_0(B_352, B_352))=k4_xboole_0(A_351, B_352))), inference(superposition, [status(thm), theory('equality')], [c_3436, c_34])).
% 7.16/2.66  tff(c_80, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.16/2.66  tff(c_2575, plain, (![A_188, B_189, C_190]: (k4_xboole_0(k3_xboole_0(A_188, B_189), k3_xboole_0(A_188, C_190))=k3_xboole_0(A_188, k4_xboole_0(B_189, C_190)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.16/2.66  tff(c_2684, plain, (![C_190]: (k4_xboole_0(k1_tarski('#skF_8'), k3_xboole_0('#skF_7', C_190))=k3_xboole_0('#skF_7', k4_xboole_0(k1_tarski('#skF_8'), C_190)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_2575])).
% 7.16/2.66  tff(c_9360, plain, (k3_xboole_0('#skF_7', k4_xboole_0(k1_tarski('#skF_8'), '#skF_7'))=k4_xboole_0(k1_tarski('#skF_8'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9301, c_2684])).
% 7.16/2.66  tff(c_9501, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3893, c_9360])).
% 7.16/2.66  tff(c_9586, plain, (![A_35]: (r1_xboole_0(k1_tarski('#skF_8'), k4_xboole_0(A_35, '#skF_7')) | ~r1_xboole_0(A_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9501, c_48])).
% 7.16/2.66  tff(c_10829, plain, (![A_366]: (r1_xboole_0(k1_tarski('#skF_8'), k4_xboole_0(A_366, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_4346, c_9586])).
% 7.16/2.66  tff(c_10889, plain, (![A_367]: (~r2_hidden('#skF_8', k4_xboole_0(A_367, '#skF_7')))), inference(resolution, [status(thm)], [c_10829, c_76])).
% 7.16/2.66  tff(c_10917, plain, (![A_3]: (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_8', A_3))), inference(resolution, [status(thm)], [c_4, c_10889])).
% 7.16/2.66  tff(c_10924, plain, (![A_368]: (~r2_hidden('#skF_8', A_368))), inference(negUnitSimplification, [status(thm)], [c_78, c_10917])).
% 7.16/2.66  tff(c_10944, plain, $false, inference(resolution, [status(thm)], [c_6469, c_10924])).
% 7.16/2.66  tff(c_10945, plain, (![A_30]: (~r1_xboole_0(A_30, k1_xboole_0))), inference(splitRight, [status(thm)], [c_224])).
% 7.16/2.66  tff(c_44, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.16/2.66  tff(c_10947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10945, c_44])).
% 7.16/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.66  
% 7.16/2.66  Inference rules
% 7.16/2.66  ----------------------
% 7.16/2.66  #Ref     : 0
% 7.16/2.66  #Sup     : 2623
% 7.16/2.66  #Fact    : 0
% 7.16/2.66  #Define  : 0
% 7.16/2.66  #Split   : 4
% 7.16/2.66  #Chain   : 0
% 7.16/2.66  #Close   : 0
% 7.16/2.66  
% 7.16/2.66  Ordering : KBO
% 7.16/2.66  
% 7.16/2.66  Simplification rules
% 7.16/2.66  ----------------------
% 7.16/2.66  #Subsume      : 722
% 7.16/2.66  #Demod        : 1322
% 7.16/2.66  #Tautology    : 994
% 7.16/2.66  #SimpNegUnit  : 60
% 7.16/2.66  #BackRed      : 10
% 7.16/2.66  
% 7.16/2.66  #Partial instantiations: 0
% 7.16/2.66  #Strategies tried      : 1
% 7.16/2.66  
% 7.16/2.66  Timing (in seconds)
% 7.16/2.66  ----------------------
% 7.16/2.66  Preprocessing        : 0.38
% 7.16/2.66  Parsing              : 0.20
% 7.16/2.66  CNF conversion       : 0.03
% 7.16/2.66  Main loop            : 1.49
% 7.16/2.66  Inferencing          : 0.44
% 7.16/2.66  Reduction            : 0.55
% 7.16/2.66  Demodulation         : 0.40
% 7.16/2.66  BG Simplification    : 0.05
% 7.16/2.66  Subsumption          : 0.34
% 7.16/2.66  Abstraction          : 0.07
% 7.16/2.66  MUC search           : 0.00
% 7.16/2.66  Cooper               : 0.00
% 7.16/2.66  Total                : 1.91
% 7.16/2.66  Index Insertion      : 0.00
% 7.16/2.66  Index Deletion       : 0.00
% 7.16/2.66  Index Matching       : 0.00
% 7.16/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:33 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 571 expanded)
%              Number of leaves         :   37 ( 215 expanded)
%              Depth                    :   17
%              Number of atoms          :  312 (1654 expanded)
%              Number of equality atoms :   38 ( 239 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_139,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_53,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_126,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_124,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_135,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ( v2_wellord1(B)
          & r1_tarski(A,k3_relat_1(B)) )
       => ( ~ ( A != k3_relat_1(B)
              & ! [C] :
                  ~ ( r2_hidden(C,k3_relat_1(B))
                    & A = k1_wellord1(B,C) ) )
        <=> ! [C] :
              ( r2_hidden(C,A)
             => ! [D] :
                  ( r2_hidden(k4_tarski(D,C),B)
                 => r2_hidden(D,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

tff(c_84,plain,(
    v3_ordinal1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_76,plain,(
    ! [A_56] :
      ( v2_wellord1(k1_wellord2(A_56))
      | ~ v3_ordinal1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_80,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_86,plain,(
    v3_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_14,plain,(
    ! [B_10,A_8] :
      ( r2_hidden(B_10,A_8)
      | B_10 = A_8
      | r2_hidden(A_8,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [A_52] : v1_relat_1(k1_wellord2(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_82,plain,(
    r4_wellord1(k1_wellord2('#skF_9'),k1_wellord2('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_137,plain,(
    ! [B_77,A_78] :
      ( r4_wellord1(B_77,A_78)
      | ~ r4_wellord1(A_78,B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_139,plain,
    ( r4_wellord1(k1_wellord2('#skF_10'),k1_wellord2('#skF_9'))
    | ~ v1_relat_1(k1_wellord2('#skF_10'))
    | ~ v1_relat_1(k1_wellord2('#skF_9')) ),
    inference(resolution,[status(thm)],[c_82,c_137])).

tff(c_142,plain,(
    r4_wellord1(k1_wellord2('#skF_10'),k1_wellord2('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_139])).

tff(c_78,plain,(
    ! [B_58,A_57] :
      ( k2_wellord1(k1_wellord2(B_58),A_57) = k1_wellord2(A_57)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_66,plain,(
    ! [A_44] :
      ( k3_relat_1(k1_wellord2(A_44)) = A_44
      | ~ v1_relat_1(k1_wellord2(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92,plain,(
    ! [A_44] : k3_relat_1(k1_wellord2(A_44)) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66])).

tff(c_74,plain,(
    ! [B_55,A_53] :
      ( k1_wellord1(k1_wellord2(B_55),A_53) = A_53
      | ~ r2_hidden(A_53,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_297,plain,(
    ! [A_106,B_107] :
      ( ~ r4_wellord1(A_106,k2_wellord1(A_106,k1_wellord1(A_106,B_107)))
      | ~ r2_hidden(B_107,k3_relat_1(A_106))
      | ~ v2_wellord1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_300,plain,(
    ! [B_55,A_53] :
      ( ~ r4_wellord1(k1_wellord2(B_55),k2_wellord1(k1_wellord2(B_55),A_53))
      | ~ r2_hidden(A_53,k3_relat_1(k1_wellord2(B_55)))
      | ~ v2_wellord1(k1_wellord2(B_55))
      | ~ v1_relat_1(k1_wellord2(B_55))
      | ~ r2_hidden(A_53,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_297])).

tff(c_480,plain,(
    ! [B_134,A_135] :
      ( ~ r4_wellord1(k1_wellord2(B_134),k2_wellord1(k1_wellord2(B_134),A_135))
      | ~ v2_wellord1(k1_wellord2(B_134))
      | ~ r2_hidden(A_135,B_134)
      | ~ v3_ordinal1(B_134)
      | ~ v3_ordinal1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92,c_300])).

tff(c_754,plain,(
    ! [B_163,A_164] :
      ( ~ r4_wellord1(k1_wellord2(B_163),k1_wellord2(A_164))
      | ~ v2_wellord1(k1_wellord2(B_163))
      | ~ r2_hidden(A_164,B_163)
      | ~ v3_ordinal1(B_163)
      | ~ v3_ordinal1(A_164)
      | ~ r1_tarski(A_164,B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_480])).

tff(c_757,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_10')
    | ~ v3_ordinal1('#skF_9')
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_142,c_754])).

tff(c_763,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_757])).

tff(c_767,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [D_22,B_18,A_11] :
      ( r2_hidden(k4_tarski(D_22,B_18),A_11)
      | ~ r2_hidden(D_22,k1_wellord1(A_11,B_18))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    ! [D_36,B_24,C_34] :
      ( r2_hidden(D_36,k3_relat_1(B_24))
      | ~ r2_hidden(k4_tarski(D_36,C_34),B_24)
      | ~ r2_hidden(C_34,k3_relat_1(B_24))
      | ~ r1_tarski(k3_relat_1(B_24),k3_relat_1(B_24))
      | ~ v2_wellord1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_398,plain,(
    ! [D_126,B_127,C_128] :
      ( r2_hidden(D_126,k3_relat_1(B_127))
      | ~ r2_hidden(k4_tarski(D_126,C_128),B_127)
      | ~ r2_hidden(C_128,k3_relat_1(B_127))
      | ~ v2_wellord1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_531,plain,(
    ! [D_142,A_143,B_144] :
      ( r2_hidden(D_142,k3_relat_1(A_143))
      | ~ r2_hidden(B_144,k3_relat_1(A_143))
      | ~ v2_wellord1(A_143)
      | ~ r2_hidden(D_142,k1_wellord1(A_143,B_144))
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_18,c_398])).

tff(c_561,plain,(
    ! [D_142,A_44,B_144] :
      ( r2_hidden(D_142,k3_relat_1(k1_wellord2(A_44)))
      | ~ r2_hidden(B_144,A_44)
      | ~ v2_wellord1(k1_wellord2(A_44))
      | ~ r2_hidden(D_142,k1_wellord1(k1_wellord2(A_44),B_144))
      | ~ v1_relat_1(k1_wellord2(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_531])).

tff(c_574,plain,(
    ! [D_145,A_146,B_147] :
      ( r2_hidden(D_145,A_146)
      | ~ r2_hidden(B_147,A_146)
      | ~ v2_wellord1(k1_wellord2(A_146))
      | ~ r2_hidden(D_145,k1_wellord1(k1_wellord2(A_146),B_147)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92,c_561])).

tff(c_1516,plain,(
    ! [A_219,B_220,B_221] :
      ( r2_hidden('#skF_1'(k1_wellord1(k1_wellord2(A_219),B_220),B_221),A_219)
      | ~ r2_hidden(B_220,A_219)
      | ~ v2_wellord1(k1_wellord2(A_219))
      | r1_tarski(k1_wellord1(k1_wellord2(A_219),B_220),B_221) ) ),
    inference(resolution,[status(thm)],[c_6,c_574])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1577,plain,(
    ! [B_222,A_223] :
      ( ~ r2_hidden(B_222,A_223)
      | ~ v2_wellord1(k1_wellord2(A_223))
      | r1_tarski(k1_wellord1(k1_wellord2(A_223),B_222),A_223) ) ),
    inference(resolution,[status(thm)],[c_1516,c_4])).

tff(c_1608,plain,(
    ! [A_224,B_225] :
      ( ~ r2_hidden(A_224,B_225)
      | ~ v2_wellord1(k1_wellord2(B_225))
      | r1_tarski(A_224,B_225)
      | ~ r2_hidden(A_224,B_225)
      | ~ v3_ordinal1(B_225)
      | ~ v3_ordinal1(A_224) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1577])).

tff(c_1723,plain,(
    ! [B_229,A_230] :
      ( ~ v2_wellord1(k1_wellord2(B_229))
      | r1_tarski(A_230,B_229)
      | ~ r2_hidden(A_230,B_229)
      | r2_hidden(B_229,A_230)
      | B_229 = A_230
      | ~ v3_ordinal1(B_229)
      | ~ v3_ordinal1(A_230) ) ),
    inference(resolution,[status(thm)],[c_14,c_1608])).

tff(c_1727,plain,(
    ! [A_231,A_232] :
      ( r1_tarski(A_231,A_232)
      | ~ r2_hidden(A_231,A_232)
      | r2_hidden(A_232,A_231)
      | A_232 = A_231
      | ~ v3_ordinal1(A_231)
      | ~ v3_ordinal1(A_232) ) ),
    inference(resolution,[status(thm)],[c_76,c_1723])).

tff(c_1791,plain,(
    ! [B_10,A_8] :
      ( r1_tarski(B_10,A_8)
      | B_10 = A_8
      | r2_hidden(A_8,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_1727])).

tff(c_1794,plain,(
    ! [B_233,A_234] :
      ( r1_tarski(B_233,A_234)
      | B_233 = A_234
      | r2_hidden(A_234,B_233)
      | ~ v3_ordinal1(B_233)
      | ~ v3_ordinal1(A_234) ) ),
    inference(resolution,[status(thm)],[c_14,c_1727])).

tff(c_1598,plain,(
    ! [A_53,B_55] :
      ( ~ r2_hidden(A_53,B_55)
      | ~ v2_wellord1(k1_wellord2(B_55))
      | r1_tarski(A_53,B_55)
      | ~ r2_hidden(A_53,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1577])).

tff(c_2138,plain,(
    ! [B_247,A_248] :
      ( ~ v2_wellord1(k1_wellord2(B_247))
      | r1_tarski(A_248,B_247)
      | ~ r2_hidden(A_248,B_247)
      | r1_tarski(B_247,A_248)
      | B_247 = A_248
      | ~ v3_ordinal1(B_247)
      | ~ v3_ordinal1(A_248) ) ),
    inference(resolution,[status(thm)],[c_1794,c_1598])).

tff(c_2142,plain,(
    ! [A_249,A_250] :
      ( r1_tarski(A_249,A_250)
      | ~ r2_hidden(A_249,A_250)
      | r1_tarski(A_250,A_249)
      | A_250 = A_249
      | ~ v3_ordinal1(A_249)
      | ~ v3_ordinal1(A_250) ) ),
    inference(resolution,[status(thm)],[c_76,c_2138])).

tff(c_2261,plain,(
    ! [A_251,B_252] :
      ( r1_tarski(A_251,B_252)
      | r1_tarski(B_252,A_251)
      | B_252 = A_251
      | ~ v3_ordinal1(B_252)
      | ~ v3_ordinal1(A_251) ) ),
    inference(resolution,[status(thm)],[c_1791,c_2142])).

tff(c_760,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_9'))
    | ~ r2_hidden('#skF_10','#skF_9')
    | ~ v3_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_10')
    | ~ r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_754])).

tff(c_766,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_9'))
    | ~ r2_hidden('#skF_10','#skF_9')
    | ~ r1_tarski('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_760])).

tff(c_768,plain,(
    ~ r1_tarski('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_766])).

tff(c_2280,plain,
    ( r1_tarski('#skF_9','#skF_10')
    | '#skF_10' = '#skF_9'
    | ~ v3_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2261,c_768])).

tff(c_2338,plain,
    ( r1_tarski('#skF_9','#skF_10')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_2280])).

tff(c_2340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_767,c_2338])).

tff(c_2341,plain,
    ( ~ r2_hidden('#skF_10','#skF_9')
    | ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_2421,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2341])).

tff(c_2424,plain,(
    ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_2421])).

tff(c_2428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2424])).

tff(c_2429,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2341])).

tff(c_2433,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_10')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_14,c_2429])).

tff(c_2439,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_2433])).

tff(c_2440,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2439])).

tff(c_2342,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2449,plain,(
    ! [B_255] :
      ( r2_hidden('#skF_9',B_255)
      | ~ r1_tarski('#skF_10',B_255) ) ),
    inference(resolution,[status(thm)],[c_2440,c_2])).

tff(c_208,plain,(
    ! [B_87,A_88] :
      ( k1_wellord1(k1_wellord2(B_87),A_88) = A_88
      | ~ r2_hidden(A_88,B_87)
      | ~ v3_ordinal1(B_87)
      | ~ v3_ordinal1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_20,plain,(
    ! [D_22,A_11] :
      ( ~ r2_hidden(D_22,k1_wellord1(A_11,D_22))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_214,plain,(
    ! [A_88,B_87] :
      ( ~ r2_hidden(A_88,A_88)
      | ~ v1_relat_1(k1_wellord2(B_87))
      | ~ r2_hidden(A_88,B_87)
      | ~ v3_ordinal1(B_87)
      | ~ v3_ordinal1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_20])).

tff(c_220,plain,(
    ! [A_88,B_87] :
      ( ~ r2_hidden(A_88,A_88)
      | ~ r2_hidden(A_88,B_87)
      | ~ v3_ordinal1(B_87)
      | ~ v3_ordinal1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_214])).

tff(c_2467,plain,(
    ! [B_87] :
      ( ~ r2_hidden('#skF_9',B_87)
      | ~ v3_ordinal1(B_87)
      | ~ v3_ordinal1('#skF_9')
      | ~ r1_tarski('#skF_10','#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2449,c_220])).

tff(c_2483,plain,(
    ! [B_256] :
      ( ~ r2_hidden('#skF_9',B_256)
      | ~ v3_ordinal1(B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2342,c_86,c_2467])).

tff(c_2489,plain,(
    ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2440,c_2483])).

tff(c_2510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2489])).

tff(c_2511,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_2592,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2511])).

tff(c_2595,plain,(
    ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_2592])).

tff(c_2599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2595])).

tff(c_2600,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_2511])).

tff(c_2512,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_159,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,A_80)
      | B_79 = A_80
      | r2_hidden(A_80,B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_176,plain,(
    ! [B_79,B_2,A_80] :
      ( r2_hidden(B_79,B_2)
      | ~ r1_tarski(A_80,B_2)
      | B_79 = A_80
      | r2_hidden(A_80,B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(A_80) ) ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_2579,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,'#skF_10')
      | B_79 = '#skF_9'
      | r2_hidden('#skF_9',B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2512,c_176])).

tff(c_2587,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,'#skF_10')
      | B_79 = '#skF_9'
      | r2_hidden('#skF_9',B_79)
      | ~ v3_ordinal1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2579])).

tff(c_2604,plain,(
    ! [B_259] :
      ( r2_hidden(B_259,'#skF_10')
      | B_259 = '#skF_9'
      | r2_hidden('#skF_9',B_259)
      | ~ v3_ordinal1(B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2579])).

tff(c_2622,plain,(
    ! [B_87] :
      ( ~ r2_hidden('#skF_10',B_87)
      | ~ v3_ordinal1(B_87)
      | '#skF_10' = '#skF_9'
      | r2_hidden('#skF_9','#skF_10')
      | ~ v3_ordinal1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2604,c_220])).

tff(c_2651,plain,(
    ! [B_87] :
      ( ~ r2_hidden('#skF_10',B_87)
      | ~ v3_ordinal1(B_87)
      | '#skF_10' = '#skF_9'
      | r2_hidden('#skF_9','#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2622])).

tff(c_2673,plain,(
    ! [B_262] :
      ( ~ r2_hidden('#skF_10',B_262)
      | ~ v3_ordinal1(B_262) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2600,c_80,c_2651])).

tff(c_2677,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2587,c_2673])).

tff(c_2696,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2677])).

tff(c_2698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2600,c_80,c_2696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.29  % Computer   : n012.cluster.edu
% 0.11/0.29  % Model      : x86_64 x86_64
% 0.11/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.29  % Memory     : 8042.1875MB
% 0.11/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.29  % CPULimit   : 60
% 0.11/0.29  % DateTime   : Tue Dec  1 17:10:52 EST 2020
% 0.11/0.29  % CPUTime    : 
% 0.11/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.95  
% 5.21/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.95  %$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 5.21/1.95  
% 5.21/1.95  %Foreground sorts:
% 5.21/1.95  
% 5.21/1.95  
% 5.21/1.95  %Background operators:
% 5.21/1.95  
% 5.21/1.95  
% 5.21/1.95  %Foreground operators:
% 5.21/1.95  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.21/1.95  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 5.21/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.21/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.21/1.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.21/1.95  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 5.21/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.21/1.95  tff('#skF_10', type, '#skF_10': $i).
% 5.21/1.95  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 5.21/1.95  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 5.21/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.21/1.95  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.21/1.95  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.21/1.95  tff('#skF_9', type, '#skF_9': $i).
% 5.21/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.21/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.21/1.95  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 5.21/1.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.21/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.21/1.95  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.21/1.95  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 5.21/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.21/1.95  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.21/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.21/1.95  
% 5.21/1.97  tff(f_153, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 5.21/1.97  tff(f_139, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 5.21/1.97  tff(f_53, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 5.21/1.97  tff(f_126, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 5.21/1.97  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 5.21/1.97  tff(f_143, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 5.21/1.97  tff(f_124, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 5.21/1.97  tff(f_135, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 5.21/1.97  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 5.21/1.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.21/1.97  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 5.21/1.97  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.21/1.97  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ((v2_wellord1(B) & r1_tarski(A, k3_relat_1(B))) => (~(~(A = k3_relat_1(B)) & (![C]: ~(r2_hidden(C, k3_relat_1(B)) & (A = k1_wellord1(B, C))))) <=> (![C]: (r2_hidden(C, A) => (![D]: (r2_hidden(k4_tarski(D, C), B) => r2_hidden(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 5.21/1.97  tff(c_84, plain, (v3_ordinal1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.21/1.97  tff(c_76, plain, (![A_56]: (v2_wellord1(k1_wellord2(A_56)) | ~v3_ordinal1(A_56))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.21/1.97  tff(c_80, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.21/1.97  tff(c_86, plain, (v3_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.21/1.97  tff(c_14, plain, (![B_10, A_8]: (r2_hidden(B_10, A_8) | B_10=A_8 | r2_hidden(A_8, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.21/1.97  tff(c_72, plain, (![A_52]: (v1_relat_1(k1_wellord2(A_52)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.21/1.97  tff(c_82, plain, (r4_wellord1(k1_wellord2('#skF_9'), k1_wellord2('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.21/1.97  tff(c_137, plain, (![B_77, A_78]: (r4_wellord1(B_77, A_78) | ~r4_wellord1(A_78, B_77) | ~v1_relat_1(B_77) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.21/1.97  tff(c_139, plain, (r4_wellord1(k1_wellord2('#skF_10'), k1_wellord2('#skF_9')) | ~v1_relat_1(k1_wellord2('#skF_10')) | ~v1_relat_1(k1_wellord2('#skF_9'))), inference(resolution, [status(thm)], [c_82, c_137])).
% 5.21/1.97  tff(c_142, plain, (r4_wellord1(k1_wellord2('#skF_10'), k1_wellord2('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_139])).
% 5.21/1.97  tff(c_78, plain, (![B_58, A_57]: (k2_wellord1(k1_wellord2(B_58), A_57)=k1_wellord2(A_57) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.21/1.97  tff(c_66, plain, (![A_44]: (k3_relat_1(k1_wellord2(A_44))=A_44 | ~v1_relat_1(k1_wellord2(A_44)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.21/1.97  tff(c_92, plain, (![A_44]: (k3_relat_1(k1_wellord2(A_44))=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66])).
% 5.21/1.97  tff(c_74, plain, (![B_55, A_53]: (k1_wellord1(k1_wellord2(B_55), A_53)=A_53 | ~r2_hidden(A_53, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.21/1.97  tff(c_297, plain, (![A_106, B_107]: (~r4_wellord1(A_106, k2_wellord1(A_106, k1_wellord1(A_106, B_107))) | ~r2_hidden(B_107, k3_relat_1(A_106)) | ~v2_wellord1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.21/1.97  tff(c_300, plain, (![B_55, A_53]: (~r4_wellord1(k1_wellord2(B_55), k2_wellord1(k1_wellord2(B_55), A_53)) | ~r2_hidden(A_53, k3_relat_1(k1_wellord2(B_55))) | ~v2_wellord1(k1_wellord2(B_55)) | ~v1_relat_1(k1_wellord2(B_55)) | ~r2_hidden(A_53, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_74, c_297])).
% 5.21/1.97  tff(c_480, plain, (![B_134, A_135]: (~r4_wellord1(k1_wellord2(B_134), k2_wellord1(k1_wellord2(B_134), A_135)) | ~v2_wellord1(k1_wellord2(B_134)) | ~r2_hidden(A_135, B_134) | ~v3_ordinal1(B_134) | ~v3_ordinal1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92, c_300])).
% 5.21/1.97  tff(c_754, plain, (![B_163, A_164]: (~r4_wellord1(k1_wellord2(B_163), k1_wellord2(A_164)) | ~v2_wellord1(k1_wellord2(B_163)) | ~r2_hidden(A_164, B_163) | ~v3_ordinal1(B_163) | ~v3_ordinal1(A_164) | ~r1_tarski(A_164, B_163))), inference(superposition, [status(thm), theory('equality')], [c_78, c_480])).
% 5.21/1.97  tff(c_757, plain, (~v2_wellord1(k1_wellord2('#skF_10')) | ~r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9') | ~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_142, c_754])).
% 5.21/1.97  tff(c_763, plain, (~v2_wellord1(k1_wellord2('#skF_10')) | ~r2_hidden('#skF_9', '#skF_10') | ~r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_757])).
% 5.21/1.97  tff(c_767, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_763])).
% 5.21/1.97  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.21/1.97  tff(c_18, plain, (![D_22, B_18, A_11]: (r2_hidden(k4_tarski(D_22, B_18), A_11) | ~r2_hidden(D_22, k1_wellord1(A_11, B_18)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.21/1.97  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.21/1.97  tff(c_48, plain, (![D_36, B_24, C_34]: (r2_hidden(D_36, k3_relat_1(B_24)) | ~r2_hidden(k4_tarski(D_36, C_34), B_24) | ~r2_hidden(C_34, k3_relat_1(B_24)) | ~r1_tarski(k3_relat_1(B_24), k3_relat_1(B_24)) | ~v2_wellord1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.21/1.97  tff(c_398, plain, (![D_126, B_127, C_128]: (r2_hidden(D_126, k3_relat_1(B_127)) | ~r2_hidden(k4_tarski(D_126, C_128), B_127) | ~r2_hidden(C_128, k3_relat_1(B_127)) | ~v2_wellord1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 5.21/1.97  tff(c_531, plain, (![D_142, A_143, B_144]: (r2_hidden(D_142, k3_relat_1(A_143)) | ~r2_hidden(B_144, k3_relat_1(A_143)) | ~v2_wellord1(A_143) | ~r2_hidden(D_142, k1_wellord1(A_143, B_144)) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_18, c_398])).
% 5.21/1.97  tff(c_561, plain, (![D_142, A_44, B_144]: (r2_hidden(D_142, k3_relat_1(k1_wellord2(A_44))) | ~r2_hidden(B_144, A_44) | ~v2_wellord1(k1_wellord2(A_44)) | ~r2_hidden(D_142, k1_wellord1(k1_wellord2(A_44), B_144)) | ~v1_relat_1(k1_wellord2(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_531])).
% 5.21/1.97  tff(c_574, plain, (![D_145, A_146, B_147]: (r2_hidden(D_145, A_146) | ~r2_hidden(B_147, A_146) | ~v2_wellord1(k1_wellord2(A_146)) | ~r2_hidden(D_145, k1_wellord1(k1_wellord2(A_146), B_147)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92, c_561])).
% 5.21/1.97  tff(c_1516, plain, (![A_219, B_220, B_221]: (r2_hidden('#skF_1'(k1_wellord1(k1_wellord2(A_219), B_220), B_221), A_219) | ~r2_hidden(B_220, A_219) | ~v2_wellord1(k1_wellord2(A_219)) | r1_tarski(k1_wellord1(k1_wellord2(A_219), B_220), B_221))), inference(resolution, [status(thm)], [c_6, c_574])).
% 5.21/1.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.21/1.97  tff(c_1577, plain, (![B_222, A_223]: (~r2_hidden(B_222, A_223) | ~v2_wellord1(k1_wellord2(A_223)) | r1_tarski(k1_wellord1(k1_wellord2(A_223), B_222), A_223))), inference(resolution, [status(thm)], [c_1516, c_4])).
% 5.21/1.97  tff(c_1608, plain, (![A_224, B_225]: (~r2_hidden(A_224, B_225) | ~v2_wellord1(k1_wellord2(B_225)) | r1_tarski(A_224, B_225) | ~r2_hidden(A_224, B_225) | ~v3_ordinal1(B_225) | ~v3_ordinal1(A_224))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1577])).
% 5.21/1.97  tff(c_1723, plain, (![B_229, A_230]: (~v2_wellord1(k1_wellord2(B_229)) | r1_tarski(A_230, B_229) | ~r2_hidden(A_230, B_229) | r2_hidden(B_229, A_230) | B_229=A_230 | ~v3_ordinal1(B_229) | ~v3_ordinal1(A_230))), inference(resolution, [status(thm)], [c_14, c_1608])).
% 5.21/1.97  tff(c_1727, plain, (![A_231, A_232]: (r1_tarski(A_231, A_232) | ~r2_hidden(A_231, A_232) | r2_hidden(A_232, A_231) | A_232=A_231 | ~v3_ordinal1(A_231) | ~v3_ordinal1(A_232))), inference(resolution, [status(thm)], [c_76, c_1723])).
% 5.21/1.97  tff(c_1791, plain, (![B_10, A_8]: (r1_tarski(B_10, A_8) | B_10=A_8 | r2_hidden(A_8, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_8))), inference(resolution, [status(thm)], [c_14, c_1727])).
% 5.21/1.97  tff(c_1794, plain, (![B_233, A_234]: (r1_tarski(B_233, A_234) | B_233=A_234 | r2_hidden(A_234, B_233) | ~v3_ordinal1(B_233) | ~v3_ordinal1(A_234))), inference(resolution, [status(thm)], [c_14, c_1727])).
% 5.21/1.97  tff(c_1598, plain, (![A_53, B_55]: (~r2_hidden(A_53, B_55) | ~v2_wellord1(k1_wellord2(B_55)) | r1_tarski(A_53, B_55) | ~r2_hidden(A_53, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1577])).
% 5.21/1.97  tff(c_2138, plain, (![B_247, A_248]: (~v2_wellord1(k1_wellord2(B_247)) | r1_tarski(A_248, B_247) | ~r2_hidden(A_248, B_247) | r1_tarski(B_247, A_248) | B_247=A_248 | ~v3_ordinal1(B_247) | ~v3_ordinal1(A_248))), inference(resolution, [status(thm)], [c_1794, c_1598])).
% 5.21/1.97  tff(c_2142, plain, (![A_249, A_250]: (r1_tarski(A_249, A_250) | ~r2_hidden(A_249, A_250) | r1_tarski(A_250, A_249) | A_250=A_249 | ~v3_ordinal1(A_249) | ~v3_ordinal1(A_250))), inference(resolution, [status(thm)], [c_76, c_2138])).
% 5.21/1.97  tff(c_2261, plain, (![A_251, B_252]: (r1_tarski(A_251, B_252) | r1_tarski(B_252, A_251) | B_252=A_251 | ~v3_ordinal1(B_252) | ~v3_ordinal1(A_251))), inference(resolution, [status(thm)], [c_1791, c_2142])).
% 5.21/1.97  tff(c_760, plain, (~v2_wellord1(k1_wellord2('#skF_9')) | ~r2_hidden('#skF_10', '#skF_9') | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_10') | ~r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_82, c_754])).
% 5.21/1.97  tff(c_766, plain, (~v2_wellord1(k1_wellord2('#skF_9')) | ~r2_hidden('#skF_10', '#skF_9') | ~r1_tarski('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_760])).
% 5.21/1.97  tff(c_768, plain, (~r1_tarski('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_766])).
% 5.21/1.97  tff(c_2280, plain, (r1_tarski('#skF_9', '#skF_10') | '#skF_10'='#skF_9' | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_2261, c_768])).
% 5.21/1.97  tff(c_2338, plain, (r1_tarski('#skF_9', '#skF_10') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_2280])).
% 5.21/1.97  tff(c_2340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_767, c_2338])).
% 5.21/1.97  tff(c_2341, plain, (~r2_hidden('#skF_10', '#skF_9') | ~v2_wellord1(k1_wellord2('#skF_9'))), inference(splitRight, [status(thm)], [c_766])).
% 5.21/1.97  tff(c_2421, plain, (~v2_wellord1(k1_wellord2('#skF_9'))), inference(splitLeft, [status(thm)], [c_2341])).
% 5.21/1.97  tff(c_2424, plain, (~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_2421])).
% 5.21/1.97  tff(c_2428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_2424])).
% 5.21/1.97  tff(c_2429, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_2341])).
% 5.21/1.97  tff(c_2433, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_14, c_2429])).
% 5.21/1.97  tff(c_2439, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_2433])).
% 5.21/1.97  tff(c_2440, plain, (r2_hidden('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_80, c_2439])).
% 5.21/1.97  tff(c_2342, plain, (r1_tarski('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_766])).
% 5.21/1.97  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.21/1.97  tff(c_2449, plain, (![B_255]: (r2_hidden('#skF_9', B_255) | ~r1_tarski('#skF_10', B_255))), inference(resolution, [status(thm)], [c_2440, c_2])).
% 5.21/1.97  tff(c_208, plain, (![B_87, A_88]: (k1_wellord1(k1_wellord2(B_87), A_88)=A_88 | ~r2_hidden(A_88, B_87) | ~v3_ordinal1(B_87) | ~v3_ordinal1(A_88))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.21/1.97  tff(c_20, plain, (![D_22, A_11]: (~r2_hidden(D_22, k1_wellord1(A_11, D_22)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.21/1.97  tff(c_214, plain, (![A_88, B_87]: (~r2_hidden(A_88, A_88) | ~v1_relat_1(k1_wellord2(B_87)) | ~r2_hidden(A_88, B_87) | ~v3_ordinal1(B_87) | ~v3_ordinal1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_208, c_20])).
% 5.21/1.97  tff(c_220, plain, (![A_88, B_87]: (~r2_hidden(A_88, A_88) | ~r2_hidden(A_88, B_87) | ~v3_ordinal1(B_87) | ~v3_ordinal1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_214])).
% 5.21/1.97  tff(c_2467, plain, (![B_87]: (~r2_hidden('#skF_9', B_87) | ~v3_ordinal1(B_87) | ~v3_ordinal1('#skF_9') | ~r1_tarski('#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_2449, c_220])).
% 5.21/1.97  tff(c_2483, plain, (![B_256]: (~r2_hidden('#skF_9', B_256) | ~v3_ordinal1(B_256))), inference(demodulation, [status(thm), theory('equality')], [c_2342, c_86, c_2467])).
% 5.21/1.97  tff(c_2489, plain, (~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_2440, c_2483])).
% 5.21/1.97  tff(c_2510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_2489])).
% 5.21/1.97  tff(c_2511, plain, (~r2_hidden('#skF_9', '#skF_10') | ~v2_wellord1(k1_wellord2('#skF_10'))), inference(splitRight, [status(thm)], [c_763])).
% 5.21/1.97  tff(c_2592, plain, (~v2_wellord1(k1_wellord2('#skF_10'))), inference(splitLeft, [status(thm)], [c_2511])).
% 5.21/1.97  tff(c_2595, plain, (~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_2592])).
% 5.21/1.97  tff(c_2599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_2595])).
% 5.21/1.97  tff(c_2600, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_2511])).
% 5.21/1.97  tff(c_2512, plain, (r1_tarski('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_763])).
% 5.21/1.97  tff(c_159, plain, (![B_79, A_80]: (r2_hidden(B_79, A_80) | B_79=A_80 | r2_hidden(A_80, B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(A_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.21/1.97  tff(c_176, plain, (![B_79, B_2, A_80]: (r2_hidden(B_79, B_2) | ~r1_tarski(A_80, B_2) | B_79=A_80 | r2_hidden(A_80, B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(A_80))), inference(resolution, [status(thm)], [c_159, c_2])).
% 5.21/1.97  tff(c_2579, plain, (![B_79]: (r2_hidden(B_79, '#skF_10') | B_79='#skF_9' | r2_hidden('#skF_9', B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1('#skF_9'))), inference(resolution, [status(thm)], [c_2512, c_176])).
% 5.21/1.97  tff(c_2587, plain, (![B_79]: (r2_hidden(B_79, '#skF_10') | B_79='#skF_9' | r2_hidden('#skF_9', B_79) | ~v3_ordinal1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2579])).
% 5.21/1.97  tff(c_2604, plain, (![B_259]: (r2_hidden(B_259, '#skF_10') | B_259='#skF_9' | r2_hidden('#skF_9', B_259) | ~v3_ordinal1(B_259))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2579])).
% 5.21/1.97  tff(c_2622, plain, (![B_87]: (~r2_hidden('#skF_10', B_87) | ~v3_ordinal1(B_87) | '#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10'))), inference(resolution, [status(thm)], [c_2604, c_220])).
% 5.21/1.97  tff(c_2651, plain, (![B_87]: (~r2_hidden('#skF_10', B_87) | ~v3_ordinal1(B_87) | '#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2622])).
% 5.21/1.97  tff(c_2673, plain, (![B_262]: (~r2_hidden('#skF_10', B_262) | ~v3_ordinal1(B_262))), inference(negUnitSimplification, [status(thm)], [c_2600, c_80, c_2651])).
% 5.21/1.97  tff(c_2677, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_2587, c_2673])).
% 5.21/1.97  tff(c_2696, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2677])).
% 5.21/1.97  tff(c_2698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2600, c_80, c_2696])).
% 5.21/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.97  
% 5.21/1.97  Inference rules
% 5.21/1.97  ----------------------
% 5.21/1.97  #Ref     : 0
% 5.21/1.97  #Sup     : 575
% 5.21/1.97  #Fact    : 4
% 5.21/1.97  #Define  : 0
% 5.21/1.97  #Split   : 4
% 5.21/1.97  #Chain   : 0
% 5.21/1.97  #Close   : 0
% 5.21/1.97  
% 5.21/1.97  Ordering : KBO
% 5.21/1.97  
% 5.21/1.97  Simplification rules
% 5.21/1.97  ----------------------
% 5.21/1.97  #Subsume      : 29
% 5.21/1.97  #Demod        : 236
% 5.21/1.97  #Tautology    : 61
% 5.21/1.97  #SimpNegUnit  : 7
% 5.21/1.97  #BackRed      : 0
% 5.21/1.97  
% 5.21/1.97  #Partial instantiations: 0
% 5.21/1.97  #Strategies tried      : 1
% 5.21/1.97  
% 5.21/1.97  Timing (in seconds)
% 5.21/1.97  ----------------------
% 5.42/1.97  Preprocessing        : 0.37
% 5.42/1.97  Parsing              : 0.18
% 5.42/1.97  CNF conversion       : 0.03
% 5.42/1.97  Main loop            : 0.87
% 5.42/1.97  Inferencing          : 0.27
% 5.42/1.97  Reduction            : 0.22
% 5.42/1.97  Demodulation         : 0.15
% 5.42/1.97  BG Simplification    : 0.05
% 5.42/1.97  Subsumption          : 0.26
% 5.42/1.97  Abstraction          : 0.05
% 5.42/1.97  MUC search           : 0.00
% 5.42/1.97  Cooper               : 0.00
% 5.42/1.97  Total                : 1.28
% 5.42/1.97  Index Insertion      : 0.00
% 5.42/1.97  Index Deletion       : 0.00
% 5.42/1.97  Index Matching       : 0.00
% 5.42/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------

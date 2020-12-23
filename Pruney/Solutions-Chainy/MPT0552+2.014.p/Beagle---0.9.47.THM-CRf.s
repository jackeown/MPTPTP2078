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
% DateTime   : Thu Dec  3 10:00:58 EST 2020

% Result     : Theorem 10.99s
% Output     : CNFRefutation 10.99s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 205 expanded)
%              Number of leaves         :   32 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 ( 457 expanded)
%              Number of equality atoms :   15 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k7_relat_1(B_37,A_36),B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1100,plain,(
    ! [A_218,B_219,C_220] :
      ( r2_hidden('#skF_1'(A_218,B_219,C_220),A_218)
      | r2_hidden('#skF_2'(A_218,B_219,C_220),C_220)
      | k3_xboole_0(A_218,B_219) = C_220 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1121,plain,(
    ! [A_218,B_219] :
      ( r2_hidden('#skF_2'(A_218,B_219,A_218),A_218)
      | k3_xboole_0(A_218,B_219) = A_218 ) ),
    inference(resolution,[status(thm)],[c_1100,c_14])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1225,plain,(
    ! [A_239,B_240,C_241] :
      ( r2_hidden('#skF_1'(A_239,B_240,C_241),B_240)
      | ~ r2_hidden('#skF_2'(A_239,B_240,C_241),B_240)
      | ~ r2_hidden('#skF_2'(A_239,B_240,C_241),A_239)
      | k3_xboole_0(A_239,B_240) = C_241 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1240,plain,(
    ! [C_3,B_2] :
      ( ~ r2_hidden('#skF_2'(C_3,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(C_3,B_2,C_3),B_2)
      | k3_xboole_0(C_3,B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_16,c_1225])).

tff(c_1301,plain,(
    ! [A_250,B_251,C_252] :
      ( ~ r2_hidden('#skF_1'(A_250,B_251,C_252),C_252)
      | ~ r2_hidden('#skF_2'(A_250,B_251,C_252),B_251)
      | ~ r2_hidden('#skF_2'(A_250,B_251,C_252),A_250)
      | k3_xboole_0(A_250,B_251) = C_252 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1318,plain,(
    ! [B_253] :
      ( ~ r2_hidden('#skF_2'(B_253,B_253,B_253),B_253)
      | k3_xboole_0(B_253,B_253) = B_253 ) ),
    inference(resolution,[status(thm)],[c_1240,c_1301])).

tff(c_1339,plain,(
    ! [B_254] : k3_xboole_0(B_254,B_254) = B_254 ),
    inference(resolution,[status(thm)],[c_1121,c_1318])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1371,plain,(
    ! [B_254] : r1_tarski(B_254,B_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_20])).

tff(c_36,plain,(
    ! [C_25,A_23,B_24] :
      ( k7_relat_1(k7_relat_1(C_25,A_23),B_24) = k7_relat_1(C_25,k3_xboole_0(A_23,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1152,plain,(
    ! [C_226,A_227,D_228,B_229] :
      ( r1_tarski(k7_relat_1(C_226,A_227),k7_relat_1(D_228,B_229))
      | ~ r1_tarski(A_227,B_229)
      | ~ r1_tarski(C_226,D_228)
      | ~ v1_relat_1(D_228)
      | ~ v1_relat_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1158,plain,(
    ! [D_228,A_23,B_24,C_25,B_229] :
      ( r1_tarski(k7_relat_1(C_25,k3_xboole_0(A_23,B_24)),k7_relat_1(D_228,B_229))
      | ~ r1_tarski(B_24,B_229)
      | ~ r1_tarski(k7_relat_1(C_25,A_23),D_228)
      | ~ v1_relat_1(D_228)
      | ~ v1_relat_1(k7_relat_1(C_25,A_23))
      | ~ v1_relat_1(C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1152])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(k7_relat_1(B_32,A_31)) = k9_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_148,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k2_relat_1(A_82),k2_relat_1(B_83))
      | ~ r1_tarski(A_82,B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1600,plain,(
    ! [A_285,B_286,A_287] :
      ( r1_tarski(k2_relat_1(A_285),k9_relat_1(B_286,A_287))
      | ~ r1_tarski(A_285,k7_relat_1(B_286,A_287))
      | ~ v1_relat_1(k7_relat_1(B_286,A_287))
      | ~ v1_relat_1(A_285)
      | ~ v1_relat_1(B_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_148])).

tff(c_13432,plain,(
    ! [B_678,A_679,B_680,A_681] :
      ( r1_tarski(k9_relat_1(B_678,A_679),k9_relat_1(B_680,A_681))
      | ~ r1_tarski(k7_relat_1(B_678,A_679),k7_relat_1(B_680,A_681))
      | ~ v1_relat_1(k7_relat_1(B_680,A_681))
      | ~ v1_relat_1(k7_relat_1(B_678,A_679))
      | ~ v1_relat_1(B_680)
      | ~ v1_relat_1(B_678) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1600])).

tff(c_164,plain,(
    ! [C_86,A_87,B_88] :
      ( k7_relat_1(k7_relat_1(C_86,A_87),B_88) = k7_relat_1(C_86,k3_xboole_0(A_87,B_88))
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    ! [B_39,A_38] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_39,A_38)),k2_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_324,plain,(
    ! [C_119,A_120,B_121] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_119,k3_xboole_0(A_120,B_121))),k2_relat_1(k7_relat_1(C_119,A_120)))
      | ~ v1_relat_1(k7_relat_1(C_119,A_120))
      | ~ v1_relat_1(C_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_48])).

tff(c_841,plain,(
    ! [B_184,A_185,B_186] :
      ( r1_tarski(k9_relat_1(B_184,k3_xboole_0(A_185,B_186)),k2_relat_1(k7_relat_1(B_184,A_185)))
      | ~ v1_relat_1(k7_relat_1(B_184,A_185))
      | ~ v1_relat_1(B_184)
      | ~ v1_relat_1(B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_324])).

tff(c_1014,plain,(
    ! [B_210,A_211,B_212] :
      ( r1_tarski(k9_relat_1(B_210,k3_xboole_0(A_211,B_212)),k9_relat_1(B_210,A_211))
      | ~ v1_relat_1(k7_relat_1(B_210,A_211))
      | ~ v1_relat_1(B_210)
      | ~ v1_relat_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_841])).

tff(c_130,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(A_76,k3_xboole_0(B_77,C_78))
      | ~ r1_tarski(A_76,C_78)
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_138,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k9_relat_1('#skF_5','#skF_4'))
    | ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k9_relat_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_130,c_50])).

tff(c_223,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k9_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_1017,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1014,c_223])).

tff(c_1040,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1017])).

tff(c_1045,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1040])).

tff(c_1049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1045])).

tff(c_1050,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k9_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_13435,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_13432,c_1050])).

tff(c_13555,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13435])).

tff(c_13652,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_13555])).

tff(c_13655,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_13652])).

tff(c_13659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13655])).

tff(c_13660,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13555])).

tff(c_13662,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13660])).

tff(c_13671,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),'#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1158,c_13662])).

tff(c_13683,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),'#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1371,c_13671])).

tff(c_13687,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13683])).

tff(c_13690,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_13687])).

tff(c_13694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13690])).

tff(c_13695,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_13683])).

tff(c_13699,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_13695])).

tff(c_13703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13699])).

tff(c_13704,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13660])).

tff(c_13708,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_13704])).

tff(c_13712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13708])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.99/3.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.99/4.00  
% 10.99/4.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.99/4.00  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 10.99/4.00  
% 10.99/4.00  %Foreground sorts:
% 10.99/4.00  
% 10.99/4.00  
% 10.99/4.00  %Background operators:
% 10.99/4.00  
% 10.99/4.00  
% 10.99/4.00  %Foreground operators:
% 10.99/4.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.99/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.99/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.99/4.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.99/4.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.99/4.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.99/4.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.99/4.00  tff('#skF_5', type, '#skF_5': $i).
% 10.99/4.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.99/4.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.99/4.00  tff('#skF_3', type, '#skF_3': $i).
% 10.99/4.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.99/4.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.99/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.99/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.99/4.00  tff('#skF_4', type, '#skF_4': $i).
% 10.99/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.99/4.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.99/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.99/4.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.99/4.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.99/4.00  
% 10.99/4.01  tff(f_104, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 10.99/4.01  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 10.99/4.01  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 10.99/4.01  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 10.99/4.01  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.99/4.01  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 10.99/4.01  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 10.99/4.01  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 10.99/4.01  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 10.99/4.01  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 10.99/4.01  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 10.99/4.01  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.99/4.01  tff(c_34, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.99/4.01  tff(c_46, plain, (![B_37, A_36]: (r1_tarski(k7_relat_1(B_37, A_36), B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.99/4.01  tff(c_1100, plain, (![A_218, B_219, C_220]: (r2_hidden('#skF_1'(A_218, B_219, C_220), A_218) | r2_hidden('#skF_2'(A_218, B_219, C_220), C_220) | k3_xboole_0(A_218, B_219)=C_220)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.99/4.01  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.99/4.01  tff(c_1121, plain, (![A_218, B_219]: (r2_hidden('#skF_2'(A_218, B_219, A_218), A_218) | k3_xboole_0(A_218, B_219)=A_218)), inference(resolution, [status(thm)], [c_1100, c_14])).
% 10.99/4.01  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.99/4.01  tff(c_1225, plain, (![A_239, B_240, C_241]: (r2_hidden('#skF_1'(A_239, B_240, C_241), B_240) | ~r2_hidden('#skF_2'(A_239, B_240, C_241), B_240) | ~r2_hidden('#skF_2'(A_239, B_240, C_241), A_239) | k3_xboole_0(A_239, B_240)=C_241)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.99/4.01  tff(c_1240, plain, (![C_3, B_2]: (~r2_hidden('#skF_2'(C_3, B_2, C_3), B_2) | r2_hidden('#skF_1'(C_3, B_2, C_3), B_2) | k3_xboole_0(C_3, B_2)=C_3)), inference(resolution, [status(thm)], [c_16, c_1225])).
% 10.99/4.01  tff(c_1301, plain, (![A_250, B_251, C_252]: (~r2_hidden('#skF_1'(A_250, B_251, C_252), C_252) | ~r2_hidden('#skF_2'(A_250, B_251, C_252), B_251) | ~r2_hidden('#skF_2'(A_250, B_251, C_252), A_250) | k3_xboole_0(A_250, B_251)=C_252)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.99/4.01  tff(c_1318, plain, (![B_253]: (~r2_hidden('#skF_2'(B_253, B_253, B_253), B_253) | k3_xboole_0(B_253, B_253)=B_253)), inference(resolution, [status(thm)], [c_1240, c_1301])).
% 10.99/4.01  tff(c_1339, plain, (![B_254]: (k3_xboole_0(B_254, B_254)=B_254)), inference(resolution, [status(thm)], [c_1121, c_1318])).
% 10.99/4.01  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.99/4.01  tff(c_1371, plain, (![B_254]: (r1_tarski(B_254, B_254))), inference(superposition, [status(thm), theory('equality')], [c_1339, c_20])).
% 10.99/4.01  tff(c_36, plain, (![C_25, A_23, B_24]: (k7_relat_1(k7_relat_1(C_25, A_23), B_24)=k7_relat_1(C_25, k3_xboole_0(A_23, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.99/4.01  tff(c_1152, plain, (![C_226, A_227, D_228, B_229]: (r1_tarski(k7_relat_1(C_226, A_227), k7_relat_1(D_228, B_229)) | ~r1_tarski(A_227, B_229) | ~r1_tarski(C_226, D_228) | ~v1_relat_1(D_228) | ~v1_relat_1(C_226))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.99/4.01  tff(c_1158, plain, (![D_228, A_23, B_24, C_25, B_229]: (r1_tarski(k7_relat_1(C_25, k3_xboole_0(A_23, B_24)), k7_relat_1(D_228, B_229)) | ~r1_tarski(B_24, B_229) | ~r1_tarski(k7_relat_1(C_25, A_23), D_228) | ~v1_relat_1(D_228) | ~v1_relat_1(k7_relat_1(C_25, A_23)) | ~v1_relat_1(C_25))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1152])).
% 10.99/4.01  tff(c_40, plain, (![B_32, A_31]: (k2_relat_1(k7_relat_1(B_32, A_31))=k9_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.99/4.01  tff(c_148, plain, (![A_82, B_83]: (r1_tarski(k2_relat_1(A_82), k2_relat_1(B_83)) | ~r1_tarski(A_82, B_83) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.99/4.01  tff(c_1600, plain, (![A_285, B_286, A_287]: (r1_tarski(k2_relat_1(A_285), k9_relat_1(B_286, A_287)) | ~r1_tarski(A_285, k7_relat_1(B_286, A_287)) | ~v1_relat_1(k7_relat_1(B_286, A_287)) | ~v1_relat_1(A_285) | ~v1_relat_1(B_286))), inference(superposition, [status(thm), theory('equality')], [c_40, c_148])).
% 10.99/4.01  tff(c_13432, plain, (![B_678, A_679, B_680, A_681]: (r1_tarski(k9_relat_1(B_678, A_679), k9_relat_1(B_680, A_681)) | ~r1_tarski(k7_relat_1(B_678, A_679), k7_relat_1(B_680, A_681)) | ~v1_relat_1(k7_relat_1(B_680, A_681)) | ~v1_relat_1(k7_relat_1(B_678, A_679)) | ~v1_relat_1(B_680) | ~v1_relat_1(B_678))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1600])).
% 10.99/4.01  tff(c_164, plain, (![C_86, A_87, B_88]: (k7_relat_1(k7_relat_1(C_86, A_87), B_88)=k7_relat_1(C_86, k3_xboole_0(A_87, B_88)) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.99/4.01  tff(c_48, plain, (![B_39, A_38]: (r1_tarski(k2_relat_1(k7_relat_1(B_39, A_38)), k2_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.99/4.01  tff(c_324, plain, (![C_119, A_120, B_121]: (r1_tarski(k2_relat_1(k7_relat_1(C_119, k3_xboole_0(A_120, B_121))), k2_relat_1(k7_relat_1(C_119, A_120))) | ~v1_relat_1(k7_relat_1(C_119, A_120)) | ~v1_relat_1(C_119))), inference(superposition, [status(thm), theory('equality')], [c_164, c_48])).
% 10.99/4.01  tff(c_841, plain, (![B_184, A_185, B_186]: (r1_tarski(k9_relat_1(B_184, k3_xboole_0(A_185, B_186)), k2_relat_1(k7_relat_1(B_184, A_185))) | ~v1_relat_1(k7_relat_1(B_184, A_185)) | ~v1_relat_1(B_184) | ~v1_relat_1(B_184))), inference(superposition, [status(thm), theory('equality')], [c_40, c_324])).
% 10.99/4.01  tff(c_1014, plain, (![B_210, A_211, B_212]: (r1_tarski(k9_relat_1(B_210, k3_xboole_0(A_211, B_212)), k9_relat_1(B_210, A_211)) | ~v1_relat_1(k7_relat_1(B_210, A_211)) | ~v1_relat_1(B_210) | ~v1_relat_1(B_210) | ~v1_relat_1(B_210))), inference(superposition, [status(thm), theory('equality')], [c_40, c_841])).
% 10.99/4.01  tff(c_130, plain, (![A_76, B_77, C_78]: (r1_tarski(A_76, k3_xboole_0(B_77, C_78)) | ~r1_tarski(A_76, C_78) | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.99/4.01  tff(c_50, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.99/4.01  tff(c_138, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k9_relat_1('#skF_5', '#skF_4')) | ~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k9_relat_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_130, c_50])).
% 10.99/4.01  tff(c_223, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k9_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_138])).
% 10.99/4.01  tff(c_1017, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1014, c_223])).
% 10.99/4.01  tff(c_1040, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1017])).
% 10.99/4.01  tff(c_1045, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_1040])).
% 10.99/4.01  tff(c_1049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1045])).
% 10.99/4.01  tff(c_1050, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k9_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_138])).
% 10.99/4.01  tff(c_13435, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_13432, c_1050])).
% 10.99/4.01  tff(c_13555, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13435])).
% 10.99/4.01  tff(c_13652, plain, (~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_13555])).
% 10.99/4.01  tff(c_13655, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_13652])).
% 10.99/4.01  tff(c_13659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_13655])).
% 10.99/4.01  tff(c_13660, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_13555])).
% 10.99/4.01  tff(c_13662, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k7_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_13660])).
% 10.99/4.01  tff(c_13671, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1158, c_13662])).
% 10.99/4.01  tff(c_13683, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1371, c_13671])).
% 10.99/4.01  tff(c_13687, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_13683])).
% 10.99/4.01  tff(c_13690, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_13687])).
% 10.99/4.01  tff(c_13694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_13690])).
% 10.99/4.01  tff(c_13695, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_13683])).
% 10.99/4.01  tff(c_13699, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_13695])).
% 10.99/4.01  tff(c_13703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_13699])).
% 10.99/4.01  tff(c_13704, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_13660])).
% 10.99/4.01  tff(c_13708, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_13704])).
% 10.99/4.01  tff(c_13712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_13708])).
% 10.99/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.99/4.01  
% 10.99/4.01  Inference rules
% 10.99/4.01  ----------------------
% 10.99/4.01  #Ref     : 0
% 10.99/4.01  #Sup     : 3783
% 10.99/4.01  #Fact    : 0
% 10.99/4.01  #Define  : 0
% 10.99/4.01  #Split   : 5
% 10.99/4.01  #Chain   : 0
% 10.99/4.01  #Close   : 0
% 10.99/4.01  
% 10.99/4.01  Ordering : KBO
% 10.99/4.01  
% 10.99/4.01  Simplification rules
% 10.99/4.01  ----------------------
% 10.99/4.01  #Subsume      : 766
% 10.99/4.01  #Demod        : 467
% 10.99/4.01  #Tautology    : 237
% 10.99/4.01  #SimpNegUnit  : 0
% 10.99/4.01  #BackRed      : 0
% 10.99/4.01  
% 10.99/4.01  #Partial instantiations: 0
% 10.99/4.01  #Strategies tried      : 1
% 10.99/4.01  
% 10.99/4.01  Timing (in seconds)
% 10.99/4.01  ----------------------
% 10.99/4.02  Preprocessing        : 0.42
% 10.99/4.02  Parsing              : 0.18
% 10.99/4.02  CNF conversion       : 0.04
% 10.99/4.02  Main loop            : 2.82
% 10.99/4.02  Inferencing          : 0.89
% 10.99/4.02  Reduction            : 0.64
% 10.99/4.02  Demodulation         : 0.43
% 10.99/4.02  BG Simplification    : 0.13
% 10.99/4.02  Subsumption          : 1.02
% 10.99/4.02  Abstraction          : 0.14
% 10.99/4.02  MUC search           : 0.00
% 10.99/4.02  Cooper               : 0.00
% 10.99/4.02  Total                : 3.28
% 10.99/4.02  Index Insertion      : 0.00
% 10.99/4.02  Index Deletion       : 0.00
% 10.99/4.02  Index Matching       : 0.00
% 10.99/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------

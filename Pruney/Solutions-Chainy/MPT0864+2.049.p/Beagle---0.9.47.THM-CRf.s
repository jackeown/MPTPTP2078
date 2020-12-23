%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:15 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 134 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 183 expanded)
%              Number of equality atoms :   43 ( 120 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_551,plain,(
    ! [A_218,B_219,C_220,D_221] : k3_enumset1(A_218,A_218,B_219,C_220,D_221) = k2_enumset1(A_218,B_219,C_220,D_221) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_24,B_25,G_32,D_27,C_26] : r2_hidden(G_32,k3_enumset1(A_24,B_25,C_26,D_27,G_32)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_610,plain,(
    ! [D_236,A_237,B_238,C_239] : r2_hidden(D_236,k2_enumset1(A_237,B_238,C_239,D_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_32])).

tff(c_613,plain,(
    ! [C_7,A_5,B_6] : r2_hidden(C_7,k1_enumset1(A_5,B_6,C_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_610])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_24,B_25,G_32,D_27,E_28] : r2_hidden(G_32,k3_enumset1(A_24,B_25,G_32,D_27,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_575,plain,(
    ! [B_222,A_223,C_224,D_225] : r2_hidden(B_222,k2_enumset1(A_223,B_222,C_224,D_225)) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_36])).

tff(c_579,plain,(
    ! [A_226,B_227,C_228] : r2_hidden(A_226,k1_enumset1(A_226,B_227,C_228)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_575])).

tff(c_583,plain,(
    ! [A_229,B_230] : r2_hidden(A_229,k2_tarski(A_229,B_230)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_579])).

tff(c_586,plain,(
    ! [A_2] : r2_hidden(A_2,k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_583])).

tff(c_283,plain,(
    ! [A_120,B_121,C_122,D_123] : k3_enumset1(A_120,A_120,B_121,C_122,D_123) = k2_enumset1(A_120,B_121,C_122,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_24,B_25,G_32,C_26,E_28] : r2_hidden(G_32,k3_enumset1(A_24,B_25,C_26,G_32,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_292,plain,(
    ! [C_122,A_120,B_121,D_123] : r2_hidden(C_122,k2_enumset1(A_120,B_121,C_122,D_123)) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_34])).

tff(c_38,plain,(
    ! [A_24,G_32,D_27,C_26,E_28] : r2_hidden(G_32,k3_enumset1(A_24,G_32,C_26,D_27,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_307,plain,(
    ! [A_124,B_125,C_126,D_127] : r2_hidden(A_124,k2_enumset1(A_124,B_125,C_126,D_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_38])).

tff(c_311,plain,(
    ! [A_128,B_129,C_130] : r2_hidden(A_128,k1_enumset1(A_128,B_129,C_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_307])).

tff(c_315,plain,(
    ! [A_131,B_132] : r2_hidden(A_131,k2_tarski(A_131,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_311])).

tff(c_318,plain,(
    ! [A_2] : r2_hidden(A_2,k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_315])).

tff(c_76,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_90,plain,(
    ! [A_43,B_44] : k1_mcart_1(k4_tarski(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_99,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_90])).

tff(c_115,plain,(
    ! [A_46,B_47] : k2_mcart_1(k4_tarski(A_46,B_47)) = B_47 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_124,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_115])).

tff(c_74,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_137,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_124,c_74])).

tff(c_138,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_141,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_76])).

tff(c_320,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( r2_hidden(k4_tarski(A_134,B_135),k2_zfmisc_1(C_136,D_137))
      | ~ r2_hidden(B_135,D_137)
      | ~ r2_hidden(A_134,C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_352,plain,(
    ! [C_146,D_147] :
      ( r2_hidden('#skF_4',k2_zfmisc_1(C_146,D_147))
      | ~ r2_hidden('#skF_5',D_147)
      | ~ r2_hidden('#skF_4',C_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_320])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),B_49) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_135,plain,(
    ! [A_48] : k1_tarski(A_48) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_tarski(A_12),B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    ! [A_57,B_58] :
      ( ~ r1_tarski(A_57,k2_zfmisc_1(A_57,B_58))
      | k1_xboole_0 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_205,plain,(
    ! [A_12,B_58] :
      ( k1_tarski(A_12) = k1_xboole_0
      | ~ r2_hidden(A_12,k2_zfmisc_1(k1_tarski(A_12),B_58)) ) ),
    inference(resolution,[status(thm)],[c_14,c_201])).

tff(c_208,plain,(
    ! [A_12,B_58] : ~ r2_hidden(A_12,k2_zfmisc_1(k1_tarski(A_12),B_58)) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_205])).

tff(c_366,plain,(
    ! [D_147] :
      ( ~ r2_hidden('#skF_5',D_147)
      | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_352,c_208])).

tff(c_374,plain,(
    ! [D_148] : ~ r2_hidden('#skF_5',D_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_366])).

tff(c_409,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_292,c_374])).

tff(c_410,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_413,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_76])).

tff(c_587,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( r2_hidden(k4_tarski(A_231,B_232),k2_zfmisc_1(C_233,D_234))
      | ~ r2_hidden(B_232,D_234)
      | ~ r2_hidden(A_231,C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_618,plain,(
    ! [C_243,D_244] :
      ( r2_hidden('#skF_3',k2_zfmisc_1(C_243,D_244))
      | ~ r2_hidden('#skF_3',D_244)
      | ~ r2_hidden('#skF_4',C_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_587])).

tff(c_440,plain,(
    ! [A_153,B_154] :
      ( ~ r1_tarski(A_153,k2_zfmisc_1(B_154,A_153))
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_444,plain,(
    ! [A_12,B_154] :
      ( k1_tarski(A_12) = k1_xboole_0
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_154,k1_tarski(A_12))) ) ),
    inference(resolution,[status(thm)],[c_14,c_440])).

tff(c_447,plain,(
    ! [A_12,B_154] : ~ r2_hidden(A_12,k2_zfmisc_1(B_154,k1_tarski(A_12))) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_444])).

tff(c_632,plain,(
    ! [C_243] :
      ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
      | ~ r2_hidden('#skF_4',C_243) ) ),
    inference(resolution,[status(thm)],[c_618,c_447])).

tff(c_640,plain,(
    ! [C_245] : ~ r2_hidden('#skF_4',C_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_632])).

tff(c_675,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_613,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.72/1.41  
% 2.72/1.41  %Foreground sorts:
% 2.72/1.41  
% 2.72/1.41  
% 2.72/1.41  %Background operators:
% 2.72/1.41  
% 2.72/1.41  
% 2.72/1.41  %Foreground operators:
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.72/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.72/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.72/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.41  
% 2.72/1.43  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.72/1.43  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.72/1.43  tff(f_77, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.72/1.43  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.43  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.43  tff(f_97, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.72/1.43  tff(f_87, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.72/1.43  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.72/1.43  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.72/1.43  tff(f_56, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.72/1.43  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.72/1.43  tff(f_53, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.72/1.43  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.43  tff(c_551, plain, (![A_218, B_219, C_220, D_221]: (k3_enumset1(A_218, A_218, B_219, C_220, D_221)=k2_enumset1(A_218, B_219, C_220, D_221))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.43  tff(c_32, plain, (![A_24, B_25, G_32, D_27, C_26]: (r2_hidden(G_32, k3_enumset1(A_24, B_25, C_26, D_27, G_32)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.43  tff(c_610, plain, (![D_236, A_237, B_238, C_239]: (r2_hidden(D_236, k2_enumset1(A_237, B_238, C_239, D_236)))), inference(superposition, [status(thm), theory('equality')], [c_551, c_32])).
% 2.72/1.43  tff(c_613, plain, (![C_7, A_5, B_6]: (r2_hidden(C_7, k1_enumset1(A_5, B_6, C_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_610])).
% 2.72/1.43  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.43  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.43  tff(c_36, plain, (![A_24, B_25, G_32, D_27, E_28]: (r2_hidden(G_32, k3_enumset1(A_24, B_25, G_32, D_27, E_28)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.43  tff(c_575, plain, (![B_222, A_223, C_224, D_225]: (r2_hidden(B_222, k2_enumset1(A_223, B_222, C_224, D_225)))), inference(superposition, [status(thm), theory('equality')], [c_551, c_36])).
% 2.72/1.43  tff(c_579, plain, (![A_226, B_227, C_228]: (r2_hidden(A_226, k1_enumset1(A_226, B_227, C_228)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_575])).
% 2.72/1.43  tff(c_583, plain, (![A_229, B_230]: (r2_hidden(A_229, k2_tarski(A_229, B_230)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_579])).
% 2.72/1.43  tff(c_586, plain, (![A_2]: (r2_hidden(A_2, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_583])).
% 2.72/1.43  tff(c_283, plain, (![A_120, B_121, C_122, D_123]: (k3_enumset1(A_120, A_120, B_121, C_122, D_123)=k2_enumset1(A_120, B_121, C_122, D_123))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.43  tff(c_34, plain, (![A_24, B_25, G_32, C_26, E_28]: (r2_hidden(G_32, k3_enumset1(A_24, B_25, C_26, G_32, E_28)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.43  tff(c_292, plain, (![C_122, A_120, B_121, D_123]: (r2_hidden(C_122, k2_enumset1(A_120, B_121, C_122, D_123)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_34])).
% 2.72/1.43  tff(c_38, plain, (![A_24, G_32, D_27, C_26, E_28]: (r2_hidden(G_32, k3_enumset1(A_24, G_32, C_26, D_27, E_28)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.43  tff(c_307, plain, (![A_124, B_125, C_126, D_127]: (r2_hidden(A_124, k2_enumset1(A_124, B_125, C_126, D_127)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_38])).
% 2.72/1.43  tff(c_311, plain, (![A_128, B_129, C_130]: (r2_hidden(A_128, k1_enumset1(A_128, B_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_307])).
% 2.72/1.43  tff(c_315, plain, (![A_131, B_132]: (r2_hidden(A_131, k2_tarski(A_131, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_311])).
% 2.72/1.43  tff(c_318, plain, (![A_2]: (r2_hidden(A_2, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_315])).
% 2.72/1.43  tff(c_76, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.72/1.43  tff(c_90, plain, (![A_43, B_44]: (k1_mcart_1(k4_tarski(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.72/1.43  tff(c_99, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_76, c_90])).
% 2.72/1.43  tff(c_115, plain, (![A_46, B_47]: (k2_mcart_1(k4_tarski(A_46, B_47))=B_47)), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.72/1.43  tff(c_124, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_76, c_115])).
% 2.72/1.43  tff(c_74, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.72/1.43  tff(c_137, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_124, c_74])).
% 2.72/1.43  tff(c_138, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_137])).
% 2.72/1.43  tff(c_141, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_76])).
% 2.72/1.43  tff(c_320, plain, (![A_134, B_135, C_136, D_137]: (r2_hidden(k4_tarski(A_134, B_135), k2_zfmisc_1(C_136, D_137)) | ~r2_hidden(B_135, D_137) | ~r2_hidden(A_134, C_136))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.43  tff(c_352, plain, (![C_146, D_147]: (r2_hidden('#skF_4', k2_zfmisc_1(C_146, D_147)) | ~r2_hidden('#skF_5', D_147) | ~r2_hidden('#skF_4', C_146))), inference(superposition, [status(thm), theory('equality')], [c_141, c_320])).
% 2.72/1.43  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.43  tff(c_131, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.43  tff(c_135, plain, (![A_48]: (k1_tarski(A_48)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 2.72/1.43  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.43  tff(c_201, plain, (![A_57, B_58]: (~r1_tarski(A_57, k2_zfmisc_1(A_57, B_58)) | k1_xboole_0=A_57)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.43  tff(c_205, plain, (![A_12, B_58]: (k1_tarski(A_12)=k1_xboole_0 | ~r2_hidden(A_12, k2_zfmisc_1(k1_tarski(A_12), B_58)))), inference(resolution, [status(thm)], [c_14, c_201])).
% 2.72/1.43  tff(c_208, plain, (![A_12, B_58]: (~r2_hidden(A_12, k2_zfmisc_1(k1_tarski(A_12), B_58)))), inference(negUnitSimplification, [status(thm)], [c_135, c_205])).
% 2.72/1.43  tff(c_366, plain, (![D_147]: (~r2_hidden('#skF_5', D_147) | ~r2_hidden('#skF_4', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_352, c_208])).
% 2.72/1.43  tff(c_374, plain, (![D_148]: (~r2_hidden('#skF_5', D_148))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_366])).
% 2.72/1.43  tff(c_409, plain, $false, inference(resolution, [status(thm)], [c_292, c_374])).
% 2.72/1.43  tff(c_410, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_137])).
% 2.72/1.43  tff(c_413, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_410, c_76])).
% 2.72/1.43  tff(c_587, plain, (![A_231, B_232, C_233, D_234]: (r2_hidden(k4_tarski(A_231, B_232), k2_zfmisc_1(C_233, D_234)) | ~r2_hidden(B_232, D_234) | ~r2_hidden(A_231, C_233))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.43  tff(c_618, plain, (![C_243, D_244]: (r2_hidden('#skF_3', k2_zfmisc_1(C_243, D_244)) | ~r2_hidden('#skF_3', D_244) | ~r2_hidden('#skF_4', C_243))), inference(superposition, [status(thm), theory('equality')], [c_413, c_587])).
% 2.72/1.43  tff(c_440, plain, (![A_153, B_154]: (~r1_tarski(A_153, k2_zfmisc_1(B_154, A_153)) | k1_xboole_0=A_153)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.43  tff(c_444, plain, (![A_12, B_154]: (k1_tarski(A_12)=k1_xboole_0 | ~r2_hidden(A_12, k2_zfmisc_1(B_154, k1_tarski(A_12))))), inference(resolution, [status(thm)], [c_14, c_440])).
% 2.72/1.43  tff(c_447, plain, (![A_12, B_154]: (~r2_hidden(A_12, k2_zfmisc_1(B_154, k1_tarski(A_12))))), inference(negUnitSimplification, [status(thm)], [c_135, c_444])).
% 2.72/1.43  tff(c_632, plain, (![C_243]: (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_4', C_243))), inference(resolution, [status(thm)], [c_618, c_447])).
% 2.72/1.43  tff(c_640, plain, (![C_245]: (~r2_hidden('#skF_4', C_245))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_632])).
% 2.72/1.43  tff(c_675, plain, $false, inference(resolution, [status(thm)], [c_613, c_640])).
% 2.72/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  Inference rules
% 2.72/1.43  ----------------------
% 2.72/1.43  #Ref     : 0
% 2.72/1.43  #Sup     : 147
% 2.72/1.43  #Fact    : 0
% 2.72/1.43  #Define  : 0
% 2.72/1.43  #Split   : 1
% 2.72/1.43  #Chain   : 0
% 2.72/1.43  #Close   : 0
% 2.72/1.43  
% 2.72/1.43  Ordering : KBO
% 2.72/1.43  
% 2.72/1.43  Simplification rules
% 2.72/1.43  ----------------------
% 2.72/1.43  #Subsume      : 2
% 2.72/1.43  #Demod        : 23
% 2.72/1.43  #Tautology    : 72
% 2.72/1.43  #SimpNegUnit  : 6
% 2.72/1.43  #BackRed      : 7
% 2.72/1.43  
% 2.72/1.43  #Partial instantiations: 0
% 2.72/1.43  #Strategies tried      : 1
% 2.72/1.43  
% 2.72/1.43  Timing (in seconds)
% 2.72/1.43  ----------------------
% 2.72/1.43  Preprocessing        : 0.34
% 2.72/1.43  Parsing              : 0.17
% 2.72/1.43  CNF conversion       : 0.02
% 2.72/1.43  Main loop            : 0.30
% 2.72/1.43  Inferencing          : 0.11
% 2.72/1.43  Reduction            : 0.09
% 2.72/1.43  Demodulation         : 0.06
% 2.72/1.43  BG Simplification    : 0.02
% 2.72/1.43  Subsumption          : 0.06
% 2.72/1.43  Abstraction          : 0.02
% 2.72/1.43  MUC search           : 0.00
% 2.72/1.43  Cooper               : 0.00
% 2.72/1.43  Total                : 0.68
% 2.72/1.43  Index Insertion      : 0.00
% 2.72/1.43  Index Deletion       : 0.00
% 2.72/1.43  Index Matching       : 0.00
% 2.72/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

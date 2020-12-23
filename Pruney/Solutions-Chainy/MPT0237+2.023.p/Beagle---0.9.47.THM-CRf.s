%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:48 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :   70 (  99 expanded)
%              Number of leaves         :   39 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 111 expanded)
%              Number of equality atoms :   43 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_18,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_192,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_259,plain,(
    ! [A_94,B_95] :
      ( ~ r1_xboole_0(A_94,B_95)
      | k3_xboole_0(A_94,B_95) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_192])).

tff(c_275,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_259])).

tff(c_358,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_374,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_358])).

tff(c_392,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_374])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_165,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_850,plain,(
    ! [A_141,B_142] : k3_xboole_0(k4_xboole_0(A_141,B_142),A_141) = k4_xboole_0(A_141,B_142) ),
    inference(resolution,[status(thm)],[c_16,c_165])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_274,plain,(
    ! [A_20,B_21] : k3_xboole_0(k4_xboole_0(A_20,B_21),B_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_259])).

tff(c_919,plain,(
    ! [A_143] : k4_xboole_0(A_143,A_143) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_274])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_945,plain,(
    ! [A_143] : k5_xboole_0(A_143,k1_xboole_0) = k2_xboole_0(A_143,A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_28])).

tff(c_973,plain,(
    ! [A_143] : k2_xboole_0(A_143,A_143) = A_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_945])).

tff(c_30,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_58,B_59] :
      ( k5_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k2_tarski(A_58,B_59)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(k1_tarski(A_56),k1_tarski(B_57))
      | B_57 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_125,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = A_74
      | ~ r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1324,plain,(
    ! [A_173,B_174] :
      ( k4_xboole_0(k1_tarski(A_173),k1_tarski(B_174)) = k1_tarski(A_173)
      | B_174 = A_173 ) ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_2991,plain,(
    ! [B_219,A_220] :
      ( k5_xboole_0(k1_tarski(B_219),k1_tarski(A_220)) = k2_xboole_0(k1_tarski(B_219),k1_tarski(A_220))
      | B_219 = A_220 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_28])).

tff(c_5252,plain,(
    ! [A_261,B_262] :
      ( k2_xboole_0(k1_tarski(A_261),k1_tarski(B_262)) = k2_tarski(A_261,B_262)
      | B_262 = A_261
      | B_262 = A_261 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2991])).

tff(c_44,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_51,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50])).

tff(c_5273,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5252,c_51])).

tff(c_5277,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5273,c_5273,c_51])).

tff(c_5280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_30,c_5277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/2.06  
% 4.55/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/2.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.55/2.07  
% 4.55/2.07  %Foreground sorts:
% 4.55/2.07  
% 4.55/2.07  
% 4.55/2.07  %Background operators:
% 4.55/2.07  
% 4.55/2.07  
% 4.55/2.07  %Foreground operators:
% 4.55/2.07  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.55/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.55/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.55/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.55/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.55/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.55/2.07  tff('#skF_3', type, '#skF_3': $i).
% 4.55/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/2.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.55/2.07  tff('#skF_4', type, '#skF_4': $i).
% 4.55/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.55/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.55/2.07  
% 4.90/2.08  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.90/2.08  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.90/2.08  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.90/2.08  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.90/2.08  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.90/2.08  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.90/2.08  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.90/2.08  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.90/2.08  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.90/2.08  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.90/2.08  tff(f_97, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 4.90/2.08  tff(f_92, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.90/2.08  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.90/2.08  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.90/2.08  tff(f_100, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 4.90/2.08  tff(c_18, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.90/2.08  tff(c_20, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.90/2.08  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.90/2.08  tff(c_192, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.90/2.08  tff(c_259, plain, (![A_94, B_95]: (~r1_xboole_0(A_94, B_95) | k3_xboole_0(A_94, B_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_192])).
% 4.90/2.08  tff(c_275, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_259])).
% 4.90/2.08  tff(c_358, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.90/2.08  tff(c_374, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_275, c_358])).
% 4.90/2.08  tff(c_392, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_374])).
% 4.90/2.08  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.90/2.08  tff(c_165, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=A_82 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/2.08  tff(c_850, plain, (![A_141, B_142]: (k3_xboole_0(k4_xboole_0(A_141, B_142), A_141)=k4_xboole_0(A_141, B_142))), inference(resolution, [status(thm)], [c_16, c_165])).
% 4.90/2.08  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.90/2.08  tff(c_274, plain, (![A_20, B_21]: (k3_xboole_0(k4_xboole_0(A_20, B_21), B_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_259])).
% 4.90/2.08  tff(c_919, plain, (![A_143]: (k4_xboole_0(A_143, A_143)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_850, c_274])).
% 4.90/2.08  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.90/2.08  tff(c_945, plain, (![A_143]: (k5_xboole_0(A_143, k1_xboole_0)=k2_xboole_0(A_143, A_143))), inference(superposition, [status(thm), theory('equality')], [c_919, c_28])).
% 4.90/2.08  tff(c_973, plain, (![A_143]: (k2_xboole_0(A_143, A_143)=A_143)), inference(demodulation, [status(thm), theory('equality')], [c_392, c_945])).
% 4.90/2.08  tff(c_30, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.90/2.08  tff(c_48, plain, (![A_58, B_59]: (k5_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k2_tarski(A_58, B_59) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.90/2.08  tff(c_46, plain, (![A_56, B_57]: (r1_xboole_0(k1_tarski(A_56), k1_tarski(B_57)) | B_57=A_56)), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.90/2.08  tff(c_125, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=A_74 | ~r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.90/2.08  tff(c_1324, plain, (![A_173, B_174]: (k4_xboole_0(k1_tarski(A_173), k1_tarski(B_174))=k1_tarski(A_173) | B_174=A_173)), inference(resolution, [status(thm)], [c_46, c_125])).
% 4.90/2.08  tff(c_2991, plain, (![B_219, A_220]: (k5_xboole_0(k1_tarski(B_219), k1_tarski(A_220))=k2_xboole_0(k1_tarski(B_219), k1_tarski(A_220)) | B_219=A_220)), inference(superposition, [status(thm), theory('equality')], [c_1324, c_28])).
% 4.90/2.08  tff(c_5252, plain, (![A_261, B_262]: (k2_xboole_0(k1_tarski(A_261), k1_tarski(B_262))=k2_tarski(A_261, B_262) | B_262=A_261 | B_262=A_261)), inference(superposition, [status(thm), theory('equality')], [c_48, c_2991])).
% 4.90/2.08  tff(c_44, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.90/2.08  tff(c_50, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.90/2.08  tff(c_51, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50])).
% 4.90/2.08  tff(c_5273, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5252, c_51])).
% 4.90/2.08  tff(c_5277, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5273, c_5273, c_51])).
% 4.90/2.08  tff(c_5280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_973, c_30, c_5277])).
% 4.90/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/2.08  
% 4.90/2.08  Inference rules
% 4.90/2.08  ----------------------
% 4.90/2.08  #Ref     : 0
% 4.90/2.08  #Sup     : 1227
% 4.90/2.08  #Fact    : 0
% 4.90/2.08  #Define  : 0
% 4.90/2.08  #Split   : 0
% 4.90/2.08  #Chain   : 0
% 4.90/2.08  #Close   : 0
% 4.90/2.08  
% 4.90/2.08  Ordering : KBO
% 4.90/2.08  
% 4.90/2.08  Simplification rules
% 4.90/2.08  ----------------------
% 4.90/2.08  #Subsume      : 249
% 4.90/2.08  #Demod        : 1043
% 4.90/2.08  #Tautology    : 735
% 4.90/2.08  #SimpNegUnit  : 32
% 4.90/2.08  #BackRed      : 4
% 4.90/2.08  
% 4.90/2.08  #Partial instantiations: 0
% 4.90/2.08  #Strategies tried      : 1
% 4.90/2.08  
% 4.90/2.08  Timing (in seconds)
% 4.90/2.08  ----------------------
% 4.90/2.08  Preprocessing        : 0.39
% 4.90/2.08  Parsing              : 0.21
% 4.90/2.08  CNF conversion       : 0.02
% 4.90/2.08  Main loop            : 0.82
% 4.90/2.08  Inferencing          : 0.26
% 4.90/2.08  Reduction            : 0.34
% 4.90/2.08  Demodulation         : 0.27
% 4.97/2.08  BG Simplification    : 0.03
% 4.97/2.08  Subsumption          : 0.13
% 4.97/2.08  Abstraction          : 0.04
% 4.97/2.08  MUC search           : 0.00
% 4.97/2.08  Cooper               : 0.00
% 4.97/2.08  Total                : 1.23
% 4.97/2.08  Index Insertion      : 0.00
% 4.97/2.08  Index Deletion       : 0.00
% 4.97/2.08  Index Matching       : 0.00
% 4.97/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------

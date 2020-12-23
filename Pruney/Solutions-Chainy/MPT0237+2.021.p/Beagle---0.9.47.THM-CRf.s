%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:47 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   73 (  99 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 106 expanded)
%              Number of equality atoms :   46 (  78 expanded)
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

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_20,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_160,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = A_81
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_174,plain,(
    ! [A_83] : k3_xboole_0(k1_xboole_0,A_83) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_179,plain,(
    ! [A_83] : k3_xboole_0(A_83,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_2])).

tff(c_273,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_282,plain,(
    ! [A_83] : k5_xboole_0(A_83,k1_xboole_0) = k4_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_273])).

tff(c_297,plain,(
    ! [A_83] : k5_xboole_0(A_83,k1_xboole_0) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_282])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1041,plain,(
    ! [A_160,B_161] : k3_xboole_0(k4_xboole_0(A_160,B_161),A_160) = k4_xboole_0(A_160,B_161) ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_389,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,k3_xboole_0(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_522,plain,(
    ! [A_109,B_110] :
      ( ~ r1_xboole_0(A_109,B_110)
      | k3_xboole_0(A_109,B_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_389])).

tff(c_544,plain,(
    ! [A_20,B_21] : k3_xboole_0(k4_xboole_0(A_20,B_21),B_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_522])).

tff(c_1167,plain,(
    ! [A_164] : k4_xboole_0(A_164,A_164) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_544])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1193,plain,(
    ! [A_164] : k5_xboole_0(A_164,k1_xboole_0) = k2_xboole_0(A_164,A_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_1167,c_28])).

tff(c_1221,plain,(
    ! [A_164] : k2_xboole_0(A_164,A_164) = A_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_1193])).

tff(c_30,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_134,plain,(
    ! [A_75,B_76] :
      ( r1_xboole_0(k1_tarski(A_75),k1_tarski(B_76))
      | B_76 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1298,plain,(
    ! [A_168,B_169] :
      ( k4_xboole_0(k1_tarski(A_168),k1_tarski(B_169)) = k1_tarski(A_168)
      | B_169 = A_168 ) ),
    inference(resolution,[status(thm)],[c_134,c_24])).

tff(c_3314,plain,(
    ! [B_225,A_226] :
      ( k5_xboole_0(k1_tarski(B_225),k1_tarski(A_226)) = k2_xboole_0(k1_tarski(B_225),k1_tarski(A_226))
      | B_225 = A_226 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1298,c_28])).

tff(c_48,plain,(
    ! [A_58,B_59] :
      ( k5_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k2_tarski(A_58,B_59)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5494,plain,(
    ! [B_264,A_265] :
      ( k2_xboole_0(k1_tarski(B_264),k1_tarski(A_265)) = k2_tarski(B_264,A_265)
      | B_264 = A_265
      | B_264 = A_265 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3314,c_48])).

tff(c_44,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_51,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50])).

tff(c_5515,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5494,c_51])).

tff(c_5519,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5515,c_5515,c_51])).

tff(c_5522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_30,c_5519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.89  
% 4.55/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.90  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.55/1.90  
% 4.55/1.90  %Foreground sorts:
% 4.55/1.90  
% 4.55/1.90  
% 4.55/1.90  %Background operators:
% 4.55/1.90  
% 4.55/1.90  
% 4.55/1.90  %Foreground operators:
% 4.55/1.90  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.55/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.55/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.55/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.55/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.55/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.55/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.55/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.55/1.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.55/1.90  
% 4.55/1.91  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.55/1.91  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.55/1.91  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.55/1.91  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.55/1.91  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.55/1.91  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.55/1.91  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.55/1.91  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.55/1.91  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.55/1.91  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.55/1.91  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.55/1.91  tff(f_92, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.55/1.91  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.55/1.91  tff(f_97, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 4.55/1.91  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.55/1.91  tff(f_100, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 4.55/1.91  tff(c_20, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.91  tff(c_16, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.55/1.91  tff(c_160, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=A_81 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.91  tff(c_174, plain, (![A_83]: (k3_xboole_0(k1_xboole_0, A_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_160])).
% 4.55/1.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.91  tff(c_179, plain, (![A_83]: (k3_xboole_0(A_83, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_174, c_2])).
% 4.55/1.91  tff(c_273, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.55/1.91  tff(c_282, plain, (![A_83]: (k5_xboole_0(A_83, k1_xboole_0)=k4_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_179, c_273])).
% 4.55/1.91  tff(c_297, plain, (![A_83]: (k5_xboole_0(A_83, k1_xboole_0)=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_282])).
% 4.55/1.91  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.55/1.91  tff(c_1041, plain, (![A_160, B_161]: (k3_xboole_0(k4_xboole_0(A_160, B_161), A_160)=k4_xboole_0(A_160, B_161))), inference(resolution, [status(thm)], [c_18, c_160])).
% 4.55/1.91  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.55/1.91  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.55/1.91  tff(c_389, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, k3_xboole_0(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.91  tff(c_522, plain, (![A_109, B_110]: (~r1_xboole_0(A_109, B_110) | k3_xboole_0(A_109, B_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_389])).
% 4.55/1.91  tff(c_544, plain, (![A_20, B_21]: (k3_xboole_0(k4_xboole_0(A_20, B_21), B_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_522])).
% 4.55/1.91  tff(c_1167, plain, (![A_164]: (k4_xboole_0(A_164, A_164)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1041, c_544])).
% 4.55/1.91  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.91  tff(c_1193, plain, (![A_164]: (k5_xboole_0(A_164, k1_xboole_0)=k2_xboole_0(A_164, A_164))), inference(superposition, [status(thm), theory('equality')], [c_1167, c_28])).
% 4.55/1.91  tff(c_1221, plain, (![A_164]: (k2_xboole_0(A_164, A_164)=A_164)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_1193])).
% 4.55/1.91  tff(c_30, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.55/1.91  tff(c_134, plain, (![A_75, B_76]: (r1_xboole_0(k1_tarski(A_75), k1_tarski(B_76)) | B_76=A_75)), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/1.91  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.55/1.91  tff(c_1298, plain, (![A_168, B_169]: (k4_xboole_0(k1_tarski(A_168), k1_tarski(B_169))=k1_tarski(A_168) | B_169=A_168)), inference(resolution, [status(thm)], [c_134, c_24])).
% 4.55/1.91  tff(c_3314, plain, (![B_225, A_226]: (k5_xboole_0(k1_tarski(B_225), k1_tarski(A_226))=k2_xboole_0(k1_tarski(B_225), k1_tarski(A_226)) | B_225=A_226)), inference(superposition, [status(thm), theory('equality')], [c_1298, c_28])).
% 4.55/1.91  tff(c_48, plain, (![A_58, B_59]: (k5_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k2_tarski(A_58, B_59) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.55/1.91  tff(c_5494, plain, (![B_264, A_265]: (k2_xboole_0(k1_tarski(B_264), k1_tarski(A_265))=k2_tarski(B_264, A_265) | B_264=A_265 | B_264=A_265)), inference(superposition, [status(thm), theory('equality')], [c_3314, c_48])).
% 4.55/1.91  tff(c_44, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.55/1.91  tff(c_50, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.55/1.91  tff(c_51, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50])).
% 4.55/1.91  tff(c_5515, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5494, c_51])).
% 4.55/1.91  tff(c_5519, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5515, c_5515, c_51])).
% 4.55/1.91  tff(c_5522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1221, c_30, c_5519])).
% 4.55/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.91  
% 4.55/1.91  Inference rules
% 4.55/1.91  ----------------------
% 4.55/1.91  #Ref     : 0
% 4.55/1.91  #Sup     : 1278
% 4.55/1.91  #Fact    : 0
% 4.55/1.91  #Define  : 0
% 4.55/1.91  #Split   : 0
% 4.55/1.91  #Chain   : 0
% 4.55/1.91  #Close   : 0
% 4.55/1.91  
% 4.55/1.91  Ordering : KBO
% 4.55/1.91  
% 4.55/1.91  Simplification rules
% 4.55/1.91  ----------------------
% 4.55/1.91  #Subsume      : 260
% 4.55/1.91  #Demod        : 1088
% 4.55/1.91  #Tautology    : 767
% 4.55/1.91  #SimpNegUnit  : 32
% 4.55/1.91  #BackRed      : 4
% 4.55/1.91  
% 4.55/1.91  #Partial instantiations: 0
% 4.55/1.91  #Strategies tried      : 1
% 4.55/1.91  
% 4.55/1.91  Timing (in seconds)
% 4.55/1.91  ----------------------
% 4.55/1.91  Preprocessing        : 0.32
% 4.55/1.91  Parsing              : 0.17
% 4.55/1.91  CNF conversion       : 0.02
% 4.55/1.91  Main loop            : 0.81
% 4.55/1.91  Inferencing          : 0.26
% 4.55/1.91  Reduction            : 0.34
% 4.55/1.91  Demodulation         : 0.27
% 4.55/1.91  BG Simplification    : 0.03
% 4.55/1.91  Subsumption          : 0.13
% 4.55/1.91  Abstraction          : 0.04
% 4.55/1.91  MUC search           : 0.00
% 4.55/1.91  Cooper               : 0.00
% 4.55/1.91  Total                : 1.16
% 4.55/1.91  Index Insertion      : 0.00
% 4.55/1.91  Index Deletion       : 0.00
% 4.55/1.91  Index Matching       : 0.00
% 4.55/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------

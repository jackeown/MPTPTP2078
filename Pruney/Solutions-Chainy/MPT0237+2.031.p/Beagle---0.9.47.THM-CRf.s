%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:49 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 104 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 113 expanded)
%              Number of equality atoms :   49 (  88 expanded)
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

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_272,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,k3_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_284,plain,(
    ! [A_99,B_100] :
      ( ~ r1_xboole_0(A_99,B_100)
      | k3_xboole_0(A_99,B_100) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_272])).

tff(c_296,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_284])).

tff(c_330,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_339,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_330])).

tff(c_348,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_339])).

tff(c_26,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81,plain,(
    ! [B_63,C_64] : r1_tarski(k1_tarski(B_63),k2_tarski(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84,plain,(
    ! [A_20] : r1_tarski(k1_tarski(A_20),k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_81])).

tff(c_150,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k1_xboole_0
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_171,plain,(
    ! [A_20] : k4_xboole_0(k1_tarski(A_20),k1_tarski(A_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_150])).

tff(c_400,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k4_xboole_0(B_108,A_107)) = k2_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_415,plain,(
    ! [A_20] : k2_xboole_0(k1_tarski(A_20),k1_tarski(A_20)) = k5_xboole_0(k1_tarski(A_20),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_400])).

tff(c_560,plain,(
    ! [A_119] : k2_xboole_0(k1_tarski(A_119),k1_tarski(A_119)) = k1_tarski(A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_415])).

tff(c_208,plain,(
    ! [A_87,B_88] : k3_tarski(k2_tarski(A_87,B_88)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_217,plain,(
    ! [A_20] : k3_tarski(k1_tarski(A_20)) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_208])).

tff(c_566,plain,(
    ! [A_119] : k3_tarski(k1_tarski(k1_tarski(A_119))) = k1_tarski(A_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_217])).

tff(c_52,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),k1_tarski(B_54))
      | B_54 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_136,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = A_77
      | ~ r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_902,plain,(
    ! [A_162,B_163] :
      ( k4_xboole_0(k1_tarski(A_162),k1_tarski(B_163)) = k1_tarski(A_162)
      | B_163 = A_162 ) ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1194,plain,(
    ! [B_191,A_192] :
      ( k5_xboole_0(k1_tarski(B_191),k1_tarski(A_192)) = k2_xboole_0(k1_tarski(B_191),k1_tarski(A_192))
      | B_191 = A_192 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_24])).

tff(c_54,plain,(
    ! [A_55,B_56] :
      ( k5_xboole_0(k1_tarski(A_55),k1_tarski(B_56)) = k2_tarski(A_55,B_56)
      | B_56 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1334,plain,(
    ! [B_204,A_205] :
      ( k2_xboole_0(k1_tarski(B_204),k1_tarski(A_205)) = k2_tarski(B_204,A_205)
      | B_204 = A_205
      | B_204 = A_205 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_54])).

tff(c_50,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_57,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56])).

tff(c_1364,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_57])).

tff(c_1370,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_1364,c_57])).

tff(c_1373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_217,c_26,c_1370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.56  
% 3.14/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.14/1.56  
% 3.14/1.56  %Foreground sorts:
% 3.14/1.56  
% 3.14/1.56  
% 3.14/1.56  %Background operators:
% 3.14/1.56  
% 3.14/1.56  
% 3.14/1.56  %Foreground operators:
% 3.14/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.14/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.56  
% 3.14/1.57  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.14/1.57  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.14/1.57  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.14/1.57  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.14/1.57  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.14/1.57  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.14/1.57  tff(f_94, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.14/1.57  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.14/1.57  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.14/1.57  tff(f_96, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.14/1.57  tff(f_101, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.14/1.57  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.14/1.57  tff(f_106, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.14/1.57  tff(f_109, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.14/1.57  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.57  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.57  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.14/1.57  tff(c_272, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, k3_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.57  tff(c_284, plain, (![A_99, B_100]: (~r1_xboole_0(A_99, B_100) | k3_xboole_0(A_99, B_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_272])).
% 3.14/1.57  tff(c_296, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_284])).
% 3.14/1.57  tff(c_330, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(A_103, B_104))=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.14/1.57  tff(c_339, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_296, c_330])).
% 3.14/1.57  tff(c_348, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_339])).
% 3.14/1.57  tff(c_26, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.14/1.57  tff(c_81, plain, (![B_63, C_64]: (r1_tarski(k1_tarski(B_63), k2_tarski(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.14/1.57  tff(c_84, plain, (![A_20]: (r1_tarski(k1_tarski(A_20), k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_81])).
% 3.14/1.57  tff(c_150, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k1_xboole_0 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.14/1.57  tff(c_171, plain, (![A_20]: (k4_xboole_0(k1_tarski(A_20), k1_tarski(A_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_150])).
% 3.14/1.57  tff(c_400, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k4_xboole_0(B_108, A_107))=k2_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.14/1.57  tff(c_415, plain, (![A_20]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(A_20))=k5_xboole_0(k1_tarski(A_20), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_400])).
% 3.14/1.57  tff(c_560, plain, (![A_119]: (k2_xboole_0(k1_tarski(A_119), k1_tarski(A_119))=k1_tarski(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_415])).
% 3.14/1.57  tff(c_208, plain, (![A_87, B_88]: (k3_tarski(k2_tarski(A_87, B_88))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.57  tff(c_217, plain, (![A_20]: (k3_tarski(k1_tarski(A_20))=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_26, c_208])).
% 3.14/1.57  tff(c_566, plain, (![A_119]: (k3_tarski(k1_tarski(k1_tarski(A_119)))=k1_tarski(A_119))), inference(superposition, [status(thm), theory('equality')], [c_560, c_217])).
% 3.14/1.57  tff(c_52, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), k1_tarski(B_54)) | B_54=A_53)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.14/1.57  tff(c_136, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=A_77 | ~r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.57  tff(c_902, plain, (![A_162, B_163]: (k4_xboole_0(k1_tarski(A_162), k1_tarski(B_163))=k1_tarski(A_162) | B_163=A_162)), inference(resolution, [status(thm)], [c_52, c_136])).
% 3.14/1.57  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.14/1.57  tff(c_1194, plain, (![B_191, A_192]: (k5_xboole_0(k1_tarski(B_191), k1_tarski(A_192))=k2_xboole_0(k1_tarski(B_191), k1_tarski(A_192)) | B_191=A_192)), inference(superposition, [status(thm), theory('equality')], [c_902, c_24])).
% 3.14/1.57  tff(c_54, plain, (![A_55, B_56]: (k5_xboole_0(k1_tarski(A_55), k1_tarski(B_56))=k2_tarski(A_55, B_56) | B_56=A_55)), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.14/1.57  tff(c_1334, plain, (![B_204, A_205]: (k2_xboole_0(k1_tarski(B_204), k1_tarski(A_205))=k2_tarski(B_204, A_205) | B_204=A_205 | B_204=A_205)), inference(superposition, [status(thm), theory('equality')], [c_1194, c_54])).
% 3.14/1.57  tff(c_50, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.57  tff(c_56, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.14/1.57  tff(c_57, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56])).
% 3.14/1.57  tff(c_1364, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1334, c_57])).
% 3.14/1.57  tff(c_1370, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_1364, c_57])).
% 3.14/1.57  tff(c_1373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_566, c_217, c_26, c_1370])).
% 3.14/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.57  
% 3.14/1.57  Inference rules
% 3.14/1.57  ----------------------
% 3.14/1.57  #Ref     : 0
% 3.14/1.57  #Sup     : 310
% 3.14/1.57  #Fact    : 0
% 3.14/1.57  #Define  : 0
% 3.14/1.57  #Split   : 0
% 3.14/1.57  #Chain   : 0
% 3.14/1.57  #Close   : 0
% 3.14/1.57  
% 3.14/1.57  Ordering : KBO
% 3.14/1.57  
% 3.14/1.57  Simplification rules
% 3.14/1.57  ----------------------
% 3.14/1.57  #Subsume      : 60
% 3.14/1.57  #Demod        : 131
% 3.14/1.57  #Tautology    : 194
% 3.14/1.57  #SimpNegUnit  : 12
% 3.14/1.57  #BackRed      : 1
% 3.14/1.57  
% 3.14/1.57  #Partial instantiations: 0
% 3.14/1.57  #Strategies tried      : 1
% 3.14/1.57  
% 3.14/1.57  Timing (in seconds)
% 3.14/1.57  ----------------------
% 3.14/1.58  Preprocessing        : 0.33
% 3.14/1.58  Parsing              : 0.17
% 3.14/1.58  CNF conversion       : 0.02
% 3.14/1.58  Main loop            : 0.40
% 3.14/1.58  Inferencing          : 0.16
% 3.14/1.58  Reduction            : 0.14
% 3.14/1.58  Demodulation         : 0.10
% 3.14/1.58  BG Simplification    : 0.02
% 3.14/1.58  Subsumption          : 0.06
% 3.14/1.58  Abstraction          : 0.02
% 3.14/1.58  MUC search           : 0.00
% 3.14/1.58  Cooper               : 0.00
% 3.14/1.58  Total                : 0.75
% 3.14/1.58  Index Insertion      : 0.00
% 3.14/1.58  Index Deletion       : 0.00
% 3.14/1.58  Index Matching       : 0.00
% 3.14/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

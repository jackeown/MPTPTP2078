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
% DateTime   : Thu Dec  3 09:49:49 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 116 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 121 expanded)
%              Number of equality atoms :   49 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [B_57,C_58] : r1_tarski(k1_tarski(B_57),k2_tarski(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_77,plain,(
    ! [A_15] : r1_tarski(k1_tarski(A_15),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_137,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [A_15] : k4_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_259,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_268,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_455,plain,(
    ! [A_107,B_108] : k5_xboole_0(k5_xboole_0(A_107,B_108),k3_xboole_0(A_107,B_108)) = k2_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k5_xboole_0(k5_xboole_0(A_10,B_11),C_12) = k5_xboole_0(A_10,k5_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_467,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k5_xboole_0(B_108,k3_xboole_0(A_107,B_108))) = k2_xboole_0(A_107,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_16])).

tff(c_508,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = k2_xboole_0(A_109,B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_467])).

tff(c_547,plain,(
    ! [A_15] : k2_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k5_xboole_0(k1_tarski(A_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_508])).

tff(c_580,plain,(
    ! [A_116] : k2_xboole_0(k1_tarski(A_116),k1_tarski(A_116)) = k1_tarski(A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_547])).

tff(c_200,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_209,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_200])).

tff(c_586,plain,(
    ! [A_116] : k3_tarski(k1_tarski(k1_tarski(A_116))) = k1_tarski(A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_209])).

tff(c_46,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(k1_tarski(A_48),k1_tarski(B_49))
      | B_49 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_191,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = A_80
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_198,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(k1_tarski(A_48),k1_tarski(B_49)) = k1_tarski(A_48)
      | B_49 = A_48 ) ),
    inference(resolution,[status(thm)],[c_46,c_191])).

tff(c_2386,plain,(
    ! [B_190,A_191] :
      ( k5_xboole_0(k1_tarski(B_190),k1_tarski(A_191)) = k2_xboole_0(k1_tarski(B_190),k1_tarski(A_191))
      | B_190 = A_191 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_508])).

tff(c_48,plain,(
    ! [A_50,B_51] :
      ( k5_xboole_0(k1_tarski(A_50),k1_tarski(B_51)) = k2_tarski(A_50,B_51)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3885,plain,(
    ! [B_211,A_212] :
      ( k2_xboole_0(k1_tarski(B_211),k1_tarski(A_212)) = k2_tarski(B_211,A_212)
      | B_211 = A_212
      | B_211 = A_212 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2386,c_48])).

tff(c_44,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50])).

tff(c_3915,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3885,c_51])).

tff(c_3921,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3915,c_3915,c_51])).

tff(c_3924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_209,c_20,c_3921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.50/3.07  
% 7.50/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.50/3.07  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.50/3.07  
% 7.50/3.07  %Foreground sorts:
% 7.50/3.07  
% 7.50/3.07  
% 7.50/3.07  %Background operators:
% 7.50/3.07  
% 7.50/3.07  
% 7.50/3.07  %Foreground operators:
% 7.50/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/3.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.50/3.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.50/3.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.50/3.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.50/3.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.50/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.50/3.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.50/3.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.50/3.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.50/3.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.50/3.07  tff('#skF_2', type, '#skF_2': $i).
% 7.50/3.07  tff('#skF_1', type, '#skF_1': $i).
% 7.50/3.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.50/3.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.50/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/3.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.50/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/3.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.50/3.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.50/3.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.50/3.07  
% 7.50/3.09  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.50/3.09  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.50/3.09  tff(f_72, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 7.50/3.09  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.50/3.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.50/3.09  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.50/3.09  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.50/3.09  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.50/3.09  tff(f_74, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.50/3.09  tff(f_79, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 7.50/3.09  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.50/3.09  tff(f_84, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 7.50/3.09  tff(f_87, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 7.50/3.09  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.50/3.09  tff(c_20, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.50/3.09  tff(c_74, plain, (![B_57, C_58]: (r1_tarski(k1_tarski(B_57), k2_tarski(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.50/3.09  tff(c_77, plain, (![A_15]: (r1_tarski(k1_tarski(A_15), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_74])).
% 7.50/3.09  tff(c_137, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.50/3.09  tff(c_162, plain, (![A_15]: (k4_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_137])).
% 7.50/3.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.50/3.09  tff(c_259, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.50/3.09  tff(c_268, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_259])).
% 7.50/3.09  tff(c_455, plain, (![A_107, B_108]: (k5_xboole_0(k5_xboole_0(A_107, B_108), k3_xboole_0(A_107, B_108))=k2_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.50/3.09  tff(c_16, plain, (![A_10, B_11, C_12]: (k5_xboole_0(k5_xboole_0(A_10, B_11), C_12)=k5_xboole_0(A_10, k5_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.50/3.09  tff(c_467, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k5_xboole_0(B_108, k3_xboole_0(A_107, B_108)))=k2_xboole_0(A_107, B_108))), inference(superposition, [status(thm), theory('equality')], [c_455, c_16])).
% 7.50/3.09  tff(c_508, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k4_xboole_0(B_110, A_109))=k2_xboole_0(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_467])).
% 7.50/3.09  tff(c_547, plain, (![A_15]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k5_xboole_0(k1_tarski(A_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_508])).
% 7.50/3.09  tff(c_580, plain, (![A_116]: (k2_xboole_0(k1_tarski(A_116), k1_tarski(A_116))=k1_tarski(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_547])).
% 7.50/3.09  tff(c_200, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.50/3.09  tff(c_209, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_20, c_200])).
% 7.50/3.09  tff(c_586, plain, (![A_116]: (k3_tarski(k1_tarski(k1_tarski(A_116)))=k1_tarski(A_116))), inference(superposition, [status(thm), theory('equality')], [c_580, c_209])).
% 7.50/3.09  tff(c_46, plain, (![A_48, B_49]: (r1_xboole_0(k1_tarski(A_48), k1_tarski(B_49)) | B_49=A_48)), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.50/3.09  tff(c_191, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=A_80 | ~r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.50/3.09  tff(c_198, plain, (![A_48, B_49]: (k4_xboole_0(k1_tarski(A_48), k1_tarski(B_49))=k1_tarski(A_48) | B_49=A_48)), inference(resolution, [status(thm)], [c_46, c_191])).
% 7.50/3.09  tff(c_2386, plain, (![B_190, A_191]: (k5_xboole_0(k1_tarski(B_190), k1_tarski(A_191))=k2_xboole_0(k1_tarski(B_190), k1_tarski(A_191)) | B_190=A_191)), inference(superposition, [status(thm), theory('equality')], [c_198, c_508])).
% 7.50/3.09  tff(c_48, plain, (![A_50, B_51]: (k5_xboole_0(k1_tarski(A_50), k1_tarski(B_51))=k2_tarski(A_50, B_51) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.50/3.09  tff(c_3885, plain, (![B_211, A_212]: (k2_xboole_0(k1_tarski(B_211), k1_tarski(A_212))=k2_tarski(B_211, A_212) | B_211=A_212 | B_211=A_212)), inference(superposition, [status(thm), theory('equality')], [c_2386, c_48])).
% 7.50/3.09  tff(c_44, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.50/3.09  tff(c_50, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.50/3.09  tff(c_51, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50])).
% 7.50/3.09  tff(c_3915, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3885, c_51])).
% 7.50/3.09  tff(c_3921, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3915, c_3915, c_51])).
% 7.50/3.09  tff(c_3924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_586, c_209, c_20, c_3921])).
% 7.50/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.50/3.09  
% 7.50/3.09  Inference rules
% 7.50/3.09  ----------------------
% 7.50/3.09  #Ref     : 0
% 7.50/3.09  #Sup     : 920
% 7.50/3.09  #Fact    : 0
% 7.50/3.09  #Define  : 0
% 7.50/3.09  #Split   : 0
% 7.50/3.09  #Chain   : 0
% 7.50/3.09  #Close   : 0
% 7.50/3.09  
% 7.50/3.09  Ordering : KBO
% 7.50/3.09  
% 7.50/3.09  Simplification rules
% 7.50/3.09  ----------------------
% 7.50/3.09  #Subsume      : 10
% 7.50/3.09  #Demod        : 800
% 7.50/3.09  #Tautology    : 476
% 7.50/3.09  #SimpNegUnit  : 0
% 7.50/3.09  #BackRed      : 1
% 7.50/3.09  
% 7.50/3.09  #Partial instantiations: 0
% 7.50/3.09  #Strategies tried      : 1
% 7.50/3.09  
% 7.50/3.09  Timing (in seconds)
% 7.50/3.09  ----------------------
% 7.50/3.10  Preprocessing        : 0.55
% 7.50/3.10  Parsing              : 0.28
% 7.50/3.10  CNF conversion       : 0.04
% 7.50/3.10  Main loop            : 1.58
% 7.50/3.10  Inferencing          : 0.48
% 7.50/3.10  Reduction            : 0.75
% 7.50/3.10  Demodulation         : 0.63
% 7.50/3.10  BG Simplification    : 0.08
% 7.50/3.10  Subsumption          : 0.20
% 7.50/3.10  Abstraction          : 0.10
% 7.50/3.10  MUC search           : 0.00
% 7.50/3.10  Cooper               : 0.00
% 7.50/3.10  Total                : 2.18
% 7.50/3.10  Index Insertion      : 0.00
% 7.50/3.10  Index Deletion       : 0.00
% 7.50/3.10  Index Matching       : 0.00
% 7.50/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

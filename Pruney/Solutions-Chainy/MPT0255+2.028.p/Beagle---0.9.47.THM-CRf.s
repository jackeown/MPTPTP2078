%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:42 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   55 (  62 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  53 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [B_48,C_49] : r1_tarski(k1_xboole_0,k2_tarski(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_93,plain,(
    ! [A_61] : r1_tarski(k1_xboole_0,k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_46])).

tff(c_311,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_346,plain,(
    ! [A_61] : k4_xboole_0(k1_xboole_0,k1_tarski(A_61)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_311])).

tff(c_457,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k4_xboole_0(B_94,A_93)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_481,plain,(
    ! [A_61] : k5_xboole_0(k1_tarski(A_61),k1_xboole_0) = k2_xboole_0(k1_tarski(A_61),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_457])).

tff(c_518,plain,(
    ! [A_95] : k2_xboole_0(k1_tarski(A_95),k1_xboole_0) = k1_tarski(A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_481])).

tff(c_50,plain,(
    ! [A_52,B_53] : k2_xboole_0(k1_tarski(A_52),B_53) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_526,plain,(
    ! [A_95] : k1_tarski(A_95) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_50])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_533,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_551,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_533])).

tff(c_559,plain,(
    ! [A_99] : k4_xboole_0(A_99,k1_xboole_0) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_551])).

tff(c_52,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_109,plain,(
    ! [A_66,B_67] : k3_xboole_0(A_66,k2_xboole_0(A_66,B_67)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_118,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_109])).

tff(c_121,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_118])).

tff(c_185,plain,(
    ! [B_70,C_71] : r1_tarski(k1_tarski(B_70),k2_tarski(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_194,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_185])).

tff(c_340,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_311])).

tff(c_568,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_340])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:41:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.38  
% 2.60/1.38  %Foreground sorts:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Background operators:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Foreground operators:
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.60/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.60/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.38  
% 2.60/1.39  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.60/1.39  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.60/1.39  tff(f_76, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.60/1.39  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.60/1.39  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.60/1.39  tff(f_81, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.60/1.39  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.39  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.60/1.39  tff(f_85, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.60/1.39  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.60/1.39  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.39  tff(c_88, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.39  tff(c_46, plain, (![B_48, C_49]: (r1_tarski(k1_xboole_0, k2_tarski(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.39  tff(c_93, plain, (![A_61]: (r1_tarski(k1_xboole_0, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_46])).
% 2.60/1.39  tff(c_311, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.39  tff(c_346, plain, (![A_61]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_61))=k1_xboole_0)), inference(resolution, [status(thm)], [c_93, c_311])).
% 2.60/1.39  tff(c_457, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k4_xboole_0(B_94, A_93))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.39  tff(c_481, plain, (![A_61]: (k5_xboole_0(k1_tarski(A_61), k1_xboole_0)=k2_xboole_0(k1_tarski(A_61), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_346, c_457])).
% 2.60/1.39  tff(c_518, plain, (![A_95]: (k2_xboole_0(k1_tarski(A_95), k1_xboole_0)=k1_tarski(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_481])).
% 2.60/1.39  tff(c_50, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.60/1.39  tff(c_526, plain, (![A_95]: (k1_tarski(A_95)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_518, c_50])).
% 2.60/1.39  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.39  tff(c_533, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.39  tff(c_551, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_533])).
% 2.60/1.39  tff(c_559, plain, (![A_99]: (k4_xboole_0(A_99, k1_xboole_0)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_551])).
% 2.60/1.39  tff(c_52, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.39  tff(c_109, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k2_xboole_0(A_66, B_67))=A_66)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.39  tff(c_118, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_52, c_109])).
% 2.60/1.39  tff(c_121, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_118])).
% 2.60/1.39  tff(c_185, plain, (![B_70, C_71]: (r1_tarski(k1_tarski(B_70), k2_tarski(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.39  tff(c_194, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_121, c_185])).
% 2.60/1.39  tff(c_340, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_311])).
% 2.60/1.39  tff(c_568, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_559, c_340])).
% 2.60/1.39  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_526, c_568])).
% 2.60/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  Inference rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Ref     : 0
% 2.60/1.39  #Sup     : 146
% 2.60/1.39  #Fact    : 0
% 2.60/1.39  #Define  : 0
% 2.60/1.39  #Split   : 0
% 2.60/1.39  #Chain   : 0
% 2.60/1.39  #Close   : 0
% 2.60/1.39  
% 2.60/1.39  Ordering : KBO
% 2.60/1.39  
% 2.60/1.39  Simplification rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Subsume      : 0
% 2.60/1.39  #Demod        : 52
% 2.60/1.39  #Tautology    : 100
% 2.60/1.39  #SimpNegUnit  : 1
% 2.60/1.39  #BackRed      : 1
% 2.60/1.39  
% 2.60/1.39  #Partial instantiations: 0
% 2.60/1.39  #Strategies tried      : 1
% 2.60/1.39  
% 2.60/1.39  Timing (in seconds)
% 2.60/1.39  ----------------------
% 2.60/1.39  Preprocessing        : 0.34
% 2.60/1.39  Parsing              : 0.18
% 2.60/1.39  CNF conversion       : 0.02
% 2.60/1.39  Main loop            : 0.28
% 2.60/1.39  Inferencing          : 0.10
% 2.60/1.39  Reduction            : 0.11
% 2.60/1.39  Demodulation         : 0.08
% 2.60/1.39  BG Simplification    : 0.02
% 2.60/1.39  Subsumption          : 0.04
% 2.60/1.39  Abstraction          : 0.02
% 2.60/1.39  MUC search           : 0.00
% 2.60/1.39  Cooper               : 0.00
% 2.60/1.39  Total                : 0.65
% 2.60/1.39  Index Insertion      : 0.00
% 2.60/1.40  Index Deletion       : 0.00
% 2.60/1.40  Index Matching       : 0.00
% 2.60/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:29 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  67 expanded)
%              Number of equality atoms :   30 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_37,B_38] : k2_xboole_0(k1_tarski(A_37),B_38) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [A_37] : k1_tarski(A_37) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_157,plain,(
    ! [A_64,B_65,C_66] : k2_zfmisc_1(k1_tarski(A_64),k2_tarski(B_65,C_66)) = k2_tarski(k4_tarski(A_64,B_65),k4_tarski(A_64,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_179,plain,(
    ! [A_64,C_66] : k2_zfmisc_1(k1_tarski(A_64),k2_tarski(C_66,C_66)) = k1_tarski(k4_tarski(A_64,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4])).

tff(c_213,plain,(
    ! [A_67,C_68] : k2_zfmisc_1(k1_tarski(A_67),k1_tarski(C_68)) = k1_tarski(k4_tarski(A_67,C_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_26,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k2_zfmisc_1(A_31,B_32)) = A_31
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_222,plain,(
    ! [A_67,C_68] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_67,C_68))) = k1_tarski(A_67)
      | k1_tarski(C_68) = k1_xboole_0
      | k1_tarski(A_67) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_26])).

tff(c_228,plain,(
    ! [A_67,C_68] : k1_relat_1(k1_tarski(k4_tarski(A_67,C_68))) = k1_tarski(A_67) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_222])).

tff(c_28,plain,(
    ! [A_33,B_34,C_35] : k4_tarski(k4_tarski(A_33,B_34),C_35) = k3_mcart_1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_242,plain,(
    ! [A_71,C_72] : k1_relat_1(k1_tarski(k4_tarski(A_71,C_72))) = k1_tarski(A_71) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_222])).

tff(c_251,plain,(
    ! [A_33,B_34,C_35] : k1_relat_1(k1_tarski(k3_mcart_1(A_33,B_34,C_35))) = k1_tarski(k4_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_242])).

tff(c_30,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_30])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:30:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.33  
% 2.11/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.33  
% 2.29/1.33  %Foreground sorts:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Background operators:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Foreground operators:
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.29/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.29/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.29/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.33  
% 2.29/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.29/1.34  tff(f_48, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.29/1.34  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.29/1.34  tff(f_45, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.29/1.34  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 2.29/1.34  tff(f_62, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.29/1.34  tff(f_65, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 2.29/1.34  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.34  tff(c_40, plain, (![A_37, B_38]: (k2_xboole_0(k1_tarski(A_37), B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.34  tff(c_44, plain, (![A_37]: (k1_tarski(A_37)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_40])).
% 2.29/1.34  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.34  tff(c_157, plain, (![A_64, B_65, C_66]: (k2_zfmisc_1(k1_tarski(A_64), k2_tarski(B_65, C_66))=k2_tarski(k4_tarski(A_64, B_65), k4_tarski(A_64, C_66)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.34  tff(c_179, plain, (![A_64, C_66]: (k2_zfmisc_1(k1_tarski(A_64), k2_tarski(C_66, C_66))=k1_tarski(k4_tarski(A_64, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_4])).
% 2.29/1.34  tff(c_213, plain, (![A_67, C_68]: (k2_zfmisc_1(k1_tarski(A_67), k1_tarski(C_68))=k1_tarski(k4_tarski(A_67, C_68)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_179])).
% 2.29/1.34  tff(c_26, plain, (![A_31, B_32]: (k1_relat_1(k2_zfmisc_1(A_31, B_32))=A_31 | k1_xboole_0=B_32 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.34  tff(c_222, plain, (![A_67, C_68]: (k1_relat_1(k1_tarski(k4_tarski(A_67, C_68)))=k1_tarski(A_67) | k1_tarski(C_68)=k1_xboole_0 | k1_tarski(A_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_213, c_26])).
% 2.29/1.34  tff(c_228, plain, (![A_67, C_68]: (k1_relat_1(k1_tarski(k4_tarski(A_67, C_68)))=k1_tarski(A_67))), inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_222])).
% 2.29/1.34  tff(c_28, plain, (![A_33, B_34, C_35]: (k4_tarski(k4_tarski(A_33, B_34), C_35)=k3_mcart_1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.29/1.34  tff(c_242, plain, (![A_71, C_72]: (k1_relat_1(k1_tarski(k4_tarski(A_71, C_72)))=k1_tarski(A_71))), inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_222])).
% 2.29/1.34  tff(c_251, plain, (![A_33, B_34, C_35]: (k1_relat_1(k1_tarski(k3_mcart_1(A_33, B_34, C_35)))=k1_tarski(k4_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_242])).
% 2.29/1.34  tff(c_30, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.29/1.34  tff(c_342, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_30])).
% 2.29/1.34  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_342])).
% 2.29/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.34  
% 2.29/1.34  Inference rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Ref     : 0
% 2.29/1.34  #Sup     : 72
% 2.29/1.34  #Fact    : 0
% 2.29/1.34  #Define  : 0
% 2.29/1.34  #Split   : 0
% 2.29/1.34  #Chain   : 0
% 2.29/1.34  #Close   : 0
% 2.29/1.34  
% 2.29/1.34  Ordering : KBO
% 2.29/1.34  
% 2.29/1.34  Simplification rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Subsume      : 0
% 2.29/1.34  #Demod        : 30
% 2.29/1.34  #Tautology    : 48
% 2.29/1.34  #SimpNegUnit  : 6
% 2.29/1.34  #BackRed      : 1
% 2.29/1.34  
% 2.29/1.34  #Partial instantiations: 0
% 2.29/1.34  #Strategies tried      : 1
% 2.29/1.34  
% 2.29/1.34  Timing (in seconds)
% 2.29/1.34  ----------------------
% 2.29/1.35  Preprocessing        : 0.32
% 2.29/1.35  Parsing              : 0.16
% 2.29/1.35  CNF conversion       : 0.02
% 2.29/1.35  Main loop            : 0.21
% 2.29/1.35  Inferencing          : 0.08
% 2.29/1.35  Reduction            : 0.07
% 2.29/1.35  Demodulation         : 0.06
% 2.29/1.35  BG Simplification    : 0.02
% 2.29/1.35  Subsumption          : 0.02
% 2.29/1.35  Abstraction          : 0.02
% 2.29/1.35  MUC search           : 0.00
% 2.29/1.35  Cooper               : 0.00
% 2.29/1.35  Total                : 0.55
% 2.29/1.35  Index Insertion      : 0.00
% 2.29/1.35  Index Deletion       : 0.00
% 2.29/1.35  Index Matching       : 0.00
% 2.29/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:10:28 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  39 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_59,B_60,C_61] : k2_zfmisc_1(k2_tarski(A_59,B_60),k1_tarski(C_61)) = k2_tarski(k4_tarski(A_59,C_61),k4_tarski(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_32,B_33] : v1_relat_1(k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [A_62,C_63,B_64] : v1_relat_1(k2_tarski(k4_tarski(A_62,C_63),k4_tarski(B_64,C_63))) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_20])).

tff(c_150,plain,(
    ! [A_62,C_63] : v1_relat_1(k1_tarski(k4_tarski(A_62,C_63))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_138])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_34,B_35))) = k1_tarski(A_34)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_155,plain,(
    ! [A_34,B_35] : k1_relat_1(k1_tarski(k4_tarski(A_34,B_35))) = k1_tarski(A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_24])).

tff(c_26,plain,(
    ! [A_37,B_38,C_39] : k4_tarski(k4_tarski(A_37,B_38),C_39) = k3_mcart_1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_172,plain,(
    ! [A_72,B_73] : k1_relat_1(k1_tarski(k4_tarski(A_72,B_73))) = k1_tarski(A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_24])).

tff(c_181,plain,(
    ! [A_37,B_38,C_39] : k1_relat_1(k1_tarski(k3_mcart_1(A_37,B_38,C_39))) = k1_tarski(k4_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_172])).

tff(c_28,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_331,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_28])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:33:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.26  
% 2.11/1.26  %Foreground sorts:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Background operators:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Foreground operators:
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.11/1.26  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.11/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.26  
% 2.11/1.27  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.27  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.11/1.27  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.11/1.27  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 2.11/1.27  tff(f_55, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.11/1.27  tff(f_58, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 2.11/1.27  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.27  tff(c_91, plain, (![A_59, B_60, C_61]: (k2_zfmisc_1(k2_tarski(A_59, B_60), k1_tarski(C_61))=k2_tarski(k4_tarski(A_59, C_61), k4_tarski(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.27  tff(c_20, plain, (![A_32, B_33]: (v1_relat_1(k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.27  tff(c_138, plain, (![A_62, C_63, B_64]: (v1_relat_1(k2_tarski(k4_tarski(A_62, C_63), k4_tarski(B_64, C_63))))), inference(superposition, [status(thm), theory('equality')], [c_91, c_20])).
% 2.11/1.27  tff(c_150, plain, (![A_62, C_63]: (v1_relat_1(k1_tarski(k4_tarski(A_62, C_63))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_138])).
% 2.11/1.27  tff(c_24, plain, (![A_34, B_35]: (k1_relat_1(k1_tarski(k4_tarski(A_34, B_35)))=k1_tarski(A_34) | ~v1_relat_1(k1_tarski(k4_tarski(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.11/1.27  tff(c_155, plain, (![A_34, B_35]: (k1_relat_1(k1_tarski(k4_tarski(A_34, B_35)))=k1_tarski(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_24])).
% 2.11/1.27  tff(c_26, plain, (![A_37, B_38, C_39]: (k4_tarski(k4_tarski(A_37, B_38), C_39)=k3_mcart_1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.27  tff(c_172, plain, (![A_72, B_73]: (k1_relat_1(k1_tarski(k4_tarski(A_72, B_73)))=k1_tarski(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_24])).
% 2.11/1.27  tff(c_181, plain, (![A_37, B_38, C_39]: (k1_relat_1(k1_tarski(k3_mcart_1(A_37, B_38, C_39)))=k1_tarski(k4_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_172])).
% 2.11/1.27  tff(c_28, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.27  tff(c_331, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_28])).
% 2.11/1.27  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_331])).
% 2.11/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  Inference rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Ref     : 0
% 2.11/1.27  #Sup     : 71
% 2.11/1.27  #Fact    : 0
% 2.11/1.27  #Define  : 0
% 2.11/1.27  #Split   : 0
% 2.11/1.27  #Chain   : 0
% 2.11/1.27  #Close   : 0
% 2.11/1.27  
% 2.11/1.27  Ordering : KBO
% 2.11/1.27  
% 2.11/1.27  Simplification rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Subsume      : 0
% 2.11/1.27  #Demod        : 39
% 2.11/1.27  #Tautology    : 45
% 2.11/1.27  #SimpNegUnit  : 0
% 2.11/1.27  #BackRed      : 3
% 2.11/1.27  
% 2.11/1.27  #Partial instantiations: 0
% 2.11/1.27  #Strategies tried      : 1
% 2.11/1.27  
% 2.11/1.27  Timing (in seconds)
% 2.11/1.27  ----------------------
% 2.11/1.27  Preprocessing        : 0.31
% 2.11/1.27  Parsing              : 0.16
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.20
% 2.11/1.27  Inferencing          : 0.08
% 2.11/1.27  Reduction            : 0.07
% 2.11/1.27  Demodulation         : 0.06
% 2.11/1.27  BG Simplification    : 0.02
% 2.11/1.27  Subsumption          : 0.02
% 2.11/1.27  Abstraction          : 0.02
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.53
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

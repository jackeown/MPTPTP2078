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
% DateTime   : Thu Dec  3 10:06:38 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  35 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_31] : k1_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_31] : k2_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [B_50,A_51] : k5_relat_1(k6_relat_1(B_50),k6_relat_1(A_51)) = k6_relat_1(k3_xboole_0(A_51,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_32] :
      ( k5_relat_1(A_32,k6_relat_1(k2_relat_1(A_32))) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,(
    ! [B_50] :
      ( k6_relat_1(k3_xboole_0(k2_relat_1(k6_relat_1(B_50)),B_50)) = k6_relat_1(B_50)
      | ~ v1_relat_1(k6_relat_1(B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_22])).

tff(c_128,plain,(
    ! [B_52] : k6_relat_1(k3_xboole_0(B_52,B_52)) = k6_relat_1(B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_111])).

tff(c_146,plain,(
    ! [B_52] : k3_xboole_0(B_52,B_52) = k1_relat_1(k6_relat_1(B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_18])).

tff(c_160,plain,(
    ! [B_52] : k3_xboole_0(B_52,B_52) = B_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_146])).

tff(c_188,plain,(
    ! [C_58,A_59,B_60] :
      ( k2_wellord1(k2_wellord1(C_58,A_59),B_60) = k2_wellord1(C_58,k3_xboole_0(A_59,B_60))
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    k2_wellord1(k2_wellord1('#skF_2','#skF_1'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_197,plain,
    ( k2_wellord1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_28])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_160,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.16  
% 1.85/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.85/1.17  
% 1.85/1.17  %Foreground sorts:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Background operators:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Foreground operators:
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.85/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.85/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.85/1.17  
% 1.85/1.17  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_wellord1)).
% 1.85/1.17  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.85/1.17  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.85/1.17  tff(f_51, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.85/1.17  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 1.85/1.17  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 1.85/1.17  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.17  tff(c_18, plain, (![A_31]: (k1_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.17  tff(c_16, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.17  tff(c_20, plain, (![A_31]: (k2_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.17  tff(c_100, plain, (![B_50, A_51]: (k5_relat_1(k6_relat_1(B_50), k6_relat_1(A_51))=k6_relat_1(k3_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.17  tff(c_22, plain, (![A_32]: (k5_relat_1(A_32, k6_relat_1(k2_relat_1(A_32)))=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.17  tff(c_111, plain, (![B_50]: (k6_relat_1(k3_xboole_0(k2_relat_1(k6_relat_1(B_50)), B_50))=k6_relat_1(B_50) | ~v1_relat_1(k6_relat_1(B_50)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_22])).
% 1.85/1.17  tff(c_128, plain, (![B_52]: (k6_relat_1(k3_xboole_0(B_52, B_52))=k6_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_111])).
% 1.85/1.17  tff(c_146, plain, (![B_52]: (k3_xboole_0(B_52, B_52)=k1_relat_1(k6_relat_1(B_52)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_18])).
% 1.85/1.17  tff(c_160, plain, (![B_52]: (k3_xboole_0(B_52, B_52)=B_52)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_146])).
% 1.85/1.17  tff(c_188, plain, (![C_58, A_59, B_60]: (k2_wellord1(k2_wellord1(C_58, A_59), B_60)=k2_wellord1(C_58, k3_xboole_0(A_59, B_60)) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.17  tff(c_28, plain, (k2_wellord1(k2_wellord1('#skF_2', '#skF_1'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.17  tff(c_197, plain, (k2_wellord1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_188, c_28])).
% 1.85/1.17  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_160, c_197])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 39
% 1.85/1.17  #Fact    : 0
% 1.85/1.17  #Define  : 0
% 1.85/1.17  #Split   : 0
% 1.85/1.17  #Chain   : 0
% 1.85/1.17  #Close   : 0
% 1.85/1.17  
% 1.85/1.17  Ordering : KBO
% 1.85/1.17  
% 1.85/1.17  Simplification rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Subsume      : 0
% 1.85/1.17  #Demod        : 24
% 1.85/1.17  #Tautology    : 32
% 1.85/1.17  #SimpNegUnit  : 0
% 1.85/1.17  #BackRed      : 0
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.85/1.18  Preprocessing        : 0.29
% 1.85/1.18  Parsing              : 0.16
% 1.85/1.18  CNF conversion       : 0.02
% 1.85/1.18  Main loop            : 0.12
% 1.85/1.18  Inferencing          : 0.05
% 1.85/1.18  Reduction            : 0.04
% 1.85/1.18  Demodulation         : 0.03
% 1.85/1.18  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.01
% 1.85/1.18  Abstraction          : 0.01
% 1.85/1.18  MUC search           : 0.00
% 1.85/1.18  Cooper               : 0.00
% 1.85/1.18  Total                : 0.44
% 1.85/1.18  Index Insertion      : 0.00
% 1.85/1.18  Index Deletion       : 0.00
% 1.85/1.18  Index Matching       : 0.00
% 1.85/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

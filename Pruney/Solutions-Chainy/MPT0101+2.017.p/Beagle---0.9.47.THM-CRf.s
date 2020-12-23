%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:41 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   35 (  54 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  50 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_31,B_32] : k2_xboole_0(k5_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),k5_xboole_0(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_52,plain,(
    ! [A_19,B_20] : r1_xboole_0(k3_xboole_0(A_19,B_20),k5_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_19,B_20] : k4_xboole_0(k3_xboole_0(A_19,B_20),k5_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(resolution,[status(thm)],[c_52,c_10])).

tff(c_86,plain,(
    ! [A_29,B_30] : k2_xboole_0(k4_xboole_0(A_29,B_30),k4_xboole_0(B_30,A_29)) = k5_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [B_33,A_34] : k2_xboole_0(k4_xboole_0(B_33,A_34),k4_xboole_0(A_34,B_33)) = k5_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [B_33,A_34] : k5_xboole_0(B_33,A_34) = k5_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_4])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_23,B_24] : r1_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) ),
    inference(resolution,[status(thm)],[c_52,c_6])).

tff(c_300,plain,(
    ! [A_45,B_46] : k4_xboole_0(k5_xboole_0(A_45,B_46),k3_xboole_0(A_45,B_46)) = k5_xboole_0(A_45,B_46) ),
    inference(resolution,[status(thm)],[c_68,c_10])).

tff(c_312,plain,(
    ! [A_45,B_46] : k2_xboole_0(k5_xboole_0(A_45,B_46),k4_xboole_0(k3_xboole_0(A_45,B_46),k5_xboole_0(A_45,B_46))) = k5_xboole_0(k5_xboole_0(A_45,B_46),k3_xboole_0(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_4])).

tff(c_330,plain,(
    ! [A_45,B_46] : k5_xboole_0(k3_xboole_0(A_45,B_46),k5_xboole_0(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2,c_58,c_134,c_312])).

tff(c_16,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_159,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 2.07/1.28  
% 2.07/1.28  %Foreground sorts:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Background operators:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Foreground operators:
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.28  
% 2.07/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.29  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 2.07/1.29  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.07/1.29  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.07/1.29  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.07/1.29  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.07/1.29  tff(f_44, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.07/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.29  tff(c_107, plain, (![A_31, B_32]: (k2_xboole_0(k5_xboole_0(A_31, B_32), k3_xboole_0(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.29  tff(c_122, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k5_xboole_0(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 2.07/1.29  tff(c_52, plain, (![A_19, B_20]: (r1_xboole_0(k3_xboole_0(A_19, B_20), k5_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.29  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.29  tff(c_58, plain, (![A_19, B_20]: (k4_xboole_0(k3_xboole_0(A_19, B_20), k5_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(resolution, [status(thm)], [c_52, c_10])).
% 2.07/1.29  tff(c_86, plain, (![A_29, B_30]: (k2_xboole_0(k4_xboole_0(A_29, B_30), k4_xboole_0(B_30, A_29))=k5_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.29  tff(c_128, plain, (![B_33, A_34]: (k2_xboole_0(k4_xboole_0(B_33, A_34), k4_xboole_0(A_34, B_33))=k5_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 2.07/1.29  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.29  tff(c_134, plain, (![B_33, A_34]: (k5_xboole_0(B_33, A_34)=k5_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_128, c_4])).
% 2.07/1.29  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.29  tff(c_68, plain, (![A_23, B_24]: (r1_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24)))), inference(resolution, [status(thm)], [c_52, c_6])).
% 2.07/1.29  tff(c_300, plain, (![A_45, B_46]: (k4_xboole_0(k5_xboole_0(A_45, B_46), k3_xboole_0(A_45, B_46))=k5_xboole_0(A_45, B_46))), inference(resolution, [status(thm)], [c_68, c_10])).
% 2.07/1.29  tff(c_312, plain, (![A_45, B_46]: (k2_xboole_0(k5_xboole_0(A_45, B_46), k4_xboole_0(k3_xboole_0(A_45, B_46), k5_xboole_0(A_45, B_46)))=k5_xboole_0(k5_xboole_0(A_45, B_46), k3_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_4])).
% 2.07/1.29  tff(c_330, plain, (![A_45, B_46]: (k5_xboole_0(k3_xboole_0(A_45, B_46), k5_xboole_0(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2, c_58, c_134, c_312])).
% 2.07/1.29  tff(c_16, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.29  tff(c_159, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_16])).
% 2.07/1.29  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_330, c_159])).
% 2.07/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  Inference rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Ref     : 0
% 2.07/1.29  #Sup     : 101
% 2.07/1.29  #Fact    : 0
% 2.07/1.29  #Define  : 0
% 2.07/1.29  #Split   : 0
% 2.07/1.29  #Chain   : 0
% 2.07/1.29  #Close   : 0
% 2.07/1.29  
% 2.07/1.29  Ordering : KBO
% 2.07/1.29  
% 2.07/1.29  Simplification rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Subsume      : 4
% 2.07/1.29  #Demod        : 44
% 2.07/1.29  #Tautology    : 61
% 2.07/1.29  #SimpNegUnit  : 0
% 2.07/1.29  #BackRed      : 2
% 2.07/1.29  
% 2.07/1.29  #Partial instantiations: 0
% 2.07/1.29  #Strategies tried      : 1
% 2.07/1.29  
% 2.07/1.29  Timing (in seconds)
% 2.07/1.29  ----------------------
% 2.07/1.29  Preprocessing        : 0.27
% 2.07/1.29  Parsing              : 0.15
% 2.07/1.29  CNF conversion       : 0.01
% 2.07/1.29  Main loop            : 0.24
% 2.07/1.29  Inferencing          : 0.08
% 2.07/1.29  Reduction            : 0.10
% 2.07/1.29  Demodulation         : 0.08
% 2.07/1.29  BG Simplification    : 0.01
% 2.07/1.29  Subsumption          : 0.04
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.54
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

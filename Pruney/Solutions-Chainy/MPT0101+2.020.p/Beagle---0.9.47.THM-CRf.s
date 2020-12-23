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
% DateTime   : Thu Dec  3 09:44:41 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  41 expanded)
%              Number of equality atoms :   21 (  36 expanded)
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

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_164,plain,(
    ! [A_35,B_36] : k2_xboole_0(k5_xboole_0(A_35,B_36),k3_xboole_0(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_182,plain,(
    ! [A_35,B_36] : k2_xboole_0(k3_xboole_0(A_35,B_36),k5_xboole_0(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_164])).

tff(c_129,plain,(
    ! [A_33,B_34] : k2_xboole_0(k4_xboole_0(A_33,B_34),k4_xboole_0(B_34,A_33)) = k5_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    ! [B_37,A_38] : k2_xboole_0(k4_xboole_0(B_37,A_38),k4_xboole_0(A_38,B_37)) = k5_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_191,plain,(
    ! [B_37,A_38] : k5_xboole_0(B_37,A_38) = k5_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_355,plain,(
    ! [A_47,B_48] : k4_xboole_0(k3_xboole_0(A_47,B_48),k5_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_138,plain,(
    ! [B_34,A_33] : k2_xboole_0(k4_xboole_0(B_34,A_33),k4_xboole_0(A_33,B_34)) = k5_xboole_0(A_33,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_361,plain,(
    ! [A_47,B_48] : k2_xboole_0(k3_xboole_0(A_47,B_48),k4_xboole_0(k5_xboole_0(A_47,B_48),k3_xboole_0(A_47,B_48))) = k5_xboole_0(k5_xboole_0(A_47,B_48),k3_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_138])).

tff(c_390,plain,(
    ! [A_47,B_48] : k5_xboole_0(k3_xboole_0(A_47,B_48),k5_xboole_0(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_191,c_8,c_361])).

tff(c_20,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_230,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_20])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_230])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 2.06/1.24  
% 2.06/1.24  %Foreground sorts:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Background operators:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Foreground operators:
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.24  
% 2.06/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.25  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 2.06/1.25  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.06/1.25  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.06/1.25  tff(f_31, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.06/1.25  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.06/1.25  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.06/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.25  tff(c_164, plain, (![A_35, B_36]: (k2_xboole_0(k5_xboole_0(A_35, B_36), k3_xboole_0(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.25  tff(c_182, plain, (![A_35, B_36]: (k2_xboole_0(k3_xboole_0(A_35, B_36), k5_xboole_0(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_2, c_164])).
% 2.06/1.25  tff(c_129, plain, (![A_33, B_34]: (k2_xboole_0(k4_xboole_0(A_33, B_34), k4_xboole_0(B_34, A_33))=k5_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.25  tff(c_185, plain, (![B_37, A_38]: (k2_xboole_0(k4_xboole_0(B_37, A_38), k4_xboole_0(A_38, B_37))=k5_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 2.06/1.25  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.25  tff(c_191, plain, (![B_37, A_38]: (k5_xboole_0(B_37, A_38)=k5_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_185, c_4])).
% 2.06/1.25  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.25  tff(c_6, plain, (![A_5, B_6]: (r1_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.25  tff(c_56, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.25  tff(c_355, plain, (![A_47, B_48]: (k4_xboole_0(k3_xboole_0(A_47, B_48), k5_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.06/1.25  tff(c_138, plain, (![B_34, A_33]: (k2_xboole_0(k4_xboole_0(B_34, A_33), k4_xboole_0(A_33, B_34))=k5_xboole_0(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 2.06/1.25  tff(c_361, plain, (![A_47, B_48]: (k2_xboole_0(k3_xboole_0(A_47, B_48), k4_xboole_0(k5_xboole_0(A_47, B_48), k3_xboole_0(A_47, B_48)))=k5_xboole_0(k5_xboole_0(A_47, B_48), k3_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_138])).
% 2.06/1.25  tff(c_390, plain, (![A_47, B_48]: (k5_xboole_0(k3_xboole_0(A_47, B_48), k5_xboole_0(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_191, c_8, c_361])).
% 2.06/1.25  tff(c_20, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_230, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_20])).
% 2.06/1.25  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_390, c_230])).
% 2.06/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  Inference rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Ref     : 0
% 2.06/1.25  #Sup     : 95
% 2.06/1.25  #Fact    : 0
% 2.06/1.25  #Define  : 0
% 2.06/1.25  #Split   : 0
% 2.06/1.25  #Chain   : 0
% 2.06/1.25  #Close   : 0
% 2.06/1.25  
% 2.06/1.25  Ordering : KBO
% 2.06/1.25  
% 2.06/1.25  Simplification rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Subsume      : 1
% 2.06/1.25  #Demod        : 42
% 2.06/1.25  #Tautology    : 50
% 2.06/1.25  #SimpNegUnit  : 0
% 2.06/1.25  #BackRed      : 2
% 2.06/1.25  
% 2.06/1.25  #Partial instantiations: 0
% 2.06/1.25  #Strategies tried      : 1
% 2.06/1.25  
% 2.06/1.25  Timing (in seconds)
% 2.06/1.25  ----------------------
% 2.06/1.25  Preprocessing        : 0.26
% 2.06/1.25  Parsing              : 0.15
% 2.06/1.25  CNF conversion       : 0.02
% 2.06/1.25  Main loop            : 0.23
% 2.06/1.25  Inferencing          : 0.07
% 2.06/1.25  Reduction            : 0.10
% 2.06/1.25  Demodulation         : 0.08
% 2.06/1.26  BG Simplification    : 0.01
% 2.06/1.26  Subsumption          : 0.03
% 2.06/1.26  Abstraction          : 0.01
% 2.06/1.26  MUC search           : 0.00
% 2.06/1.26  Cooper               : 0.00
% 2.06/1.26  Total                : 0.52
% 2.06/1.26  Index Insertion      : 0.00
% 2.06/1.26  Index Deletion       : 0.00
% 2.24/1.26  Index Matching       : 0.00
% 2.24/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

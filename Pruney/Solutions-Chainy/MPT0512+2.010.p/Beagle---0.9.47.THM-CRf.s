%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:58 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   30 (  42 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_14,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_63,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_66,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = k3_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6])).

tff(c_91,plain,(
    ! [A_19] : k3_xboole_0(A_19,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_71])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_19] : r1_xboole_0(A_19,k4_xboole_0(A_19,A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_8])).

tff(c_110,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_97])).

tff(c_136,plain,(
    ! [B_23,A_24] :
      ( k7_relat_1(B_23,A_24) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [B_27] :
      ( k7_relat_1(B_27,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_110,c_136])).

tff(c_175,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_172])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.13  
% 1.78/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.14  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.78/1.14  
% 1.78/1.14  %Foreground sorts:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Background operators:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Foreground operators:
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.78/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.78/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.14  
% 1.78/1.15  tff(f_44, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.78/1.15  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.78/1.15  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.78/1.15  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.78/1.15  tff(f_33, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 1.78/1.15  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.78/1.15  tff(c_14, plain, (k7_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.78/1.15  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.78/1.15  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.15  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.15  tff(c_42, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.15  tff(c_60, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_42])).
% 1.78/1.15  tff(c_63, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_60])).
% 1.78/1.15  tff(c_66, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_60])).
% 1.78/1.15  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.15  tff(c_71, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=k3_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6])).
% 1.78/1.15  tff(c_91, plain, (![A_19]: (k3_xboole_0(A_19, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_71])).
% 1.78/1.15  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.15  tff(c_97, plain, (![A_19]: (r1_xboole_0(A_19, k4_xboole_0(A_19, A_19)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_8])).
% 1.78/1.15  tff(c_110, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_97])).
% 1.78/1.15  tff(c_136, plain, (![B_23, A_24]: (k7_relat_1(B_23, A_24)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.15  tff(c_172, plain, (![B_27]: (k7_relat_1(B_27, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_110, c_136])).
% 1.78/1.15  tff(c_175, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_172])).
% 1.78/1.15  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_175])).
% 1.78/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  Inference rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Ref     : 0
% 1.78/1.15  #Sup     : 38
% 1.78/1.15  #Fact    : 0
% 1.78/1.15  #Define  : 0
% 1.78/1.15  #Split   : 0
% 1.78/1.15  #Chain   : 0
% 1.78/1.15  #Close   : 0
% 1.78/1.15  
% 1.78/1.15  Ordering : KBO
% 1.78/1.15  
% 1.78/1.15  Simplification rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Subsume      : 0
% 1.78/1.15  #Demod        : 25
% 1.78/1.15  #Tautology    : 25
% 1.78/1.15  #SimpNegUnit  : 1
% 1.78/1.15  #BackRed      : 0
% 1.78/1.15  
% 1.78/1.15  #Partial instantiations: 0
% 1.78/1.15  #Strategies tried      : 1
% 1.78/1.15  
% 1.78/1.15  Timing (in seconds)
% 1.78/1.15  ----------------------
% 1.78/1.15  Preprocessing        : 0.24
% 1.78/1.15  Parsing              : 0.14
% 1.78/1.15  CNF conversion       : 0.01
% 1.78/1.15  Main loop            : 0.13
% 1.78/1.15  Inferencing          : 0.06
% 1.78/1.15  Reduction            : 0.04
% 1.78/1.15  Demodulation         : 0.03
% 1.78/1.15  BG Simplification    : 0.01
% 1.78/1.15  Subsumption          : 0.02
% 1.78/1.15  Abstraction          : 0.01
% 1.78/1.15  MUC search           : 0.00
% 1.78/1.15  Cooper               : 0.00
% 1.78/1.15  Total                : 0.40
% 1.78/1.15  Index Insertion      : 0.00
% 1.78/1.15  Index Deletion       : 0.00
% 1.78/1.15  Index Matching       : 0.00
% 1.78/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:06 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  51 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [B_11,A_10] :
      ( k3_xboole_0(k7_relat_1(B_11,A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_69,plain,(
    ! [B_11,A_10] :
      ( k3_xboole_0(B_11,k7_relat_1(B_11,A_10)) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_12,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,(
    ! [C_30,A_31,B_32] :
      ( k3_xboole_0(k7_relat_1(C_30,A_31),k7_relat_1(C_30,B_32)) = k7_relat_1(C_30,k3_xboole_0(A_31,B_32))
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [A_12,A_31] :
      ( k7_relat_1(A_12,k3_xboole_0(A_31,k1_relat_1(A_12))) = k3_xboole_0(k7_relat_1(A_12,A_31),A_12)
      | ~ v1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_183])).

tff(c_650,plain,(
    ! [A_50,A_51] :
      ( k7_relat_1(A_50,k3_xboole_0(A_51,k1_relat_1(A_50))) = k3_xboole_0(A_50,k7_relat_1(A_50,A_51))
      | ~ v1_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_14,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_17,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_680,plain,
    ( k3_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_17])).

tff(c_706,plain,(
    k3_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_680])).

tff(c_710,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_706])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.44  
% 2.76/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.45  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.76/1.45  
% 2.76/1.45  %Foreground sorts:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Background operators:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Foreground operators:
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.45  
% 2.87/1.46  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.87/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.87/1.46  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.87/1.46  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.87/1.46  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.87/1.46  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 2.87/1.46  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.87/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.46  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.46  tff(c_64, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.46  tff(c_67, plain, (![B_11, A_10]: (k3_xboole_0(k7_relat_1(B_11, A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_10, c_64])).
% 2.87/1.46  tff(c_69, plain, (![B_11, A_10]: (k3_xboole_0(B_11, k7_relat_1(B_11, A_10))=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_67])).
% 2.87/1.46  tff(c_12, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.46  tff(c_183, plain, (![C_30, A_31, B_32]: (k3_xboole_0(k7_relat_1(C_30, A_31), k7_relat_1(C_30, B_32))=k7_relat_1(C_30, k3_xboole_0(A_31, B_32)) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.46  tff(c_207, plain, (![A_12, A_31]: (k7_relat_1(A_12, k3_xboole_0(A_31, k1_relat_1(A_12)))=k3_xboole_0(k7_relat_1(A_12, A_31), A_12) | ~v1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_183])).
% 2.87/1.46  tff(c_650, plain, (![A_50, A_51]: (k7_relat_1(A_50, k3_xboole_0(A_51, k1_relat_1(A_50)))=k3_xboole_0(A_50, k7_relat_1(A_50, A_51)) | ~v1_relat_1(A_50) | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_207])).
% 2.87/1.46  tff(c_14, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.87/1.46  tff(c_17, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.87/1.46  tff(c_680, plain, (k3_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_650, c_17])).
% 2.87/1.46  tff(c_706, plain, (k3_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_680])).
% 2.87/1.46  tff(c_710, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_69, c_706])).
% 2.87/1.46  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_710])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 190
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 0
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 19
% 2.87/1.46  #Demod        : 57
% 2.87/1.46  #Tautology    : 73
% 2.87/1.46  #SimpNegUnit  : 0
% 2.87/1.46  #BackRed      : 0
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.26
% 2.87/1.46  Parsing              : 0.15
% 2.87/1.46  CNF conversion       : 0.02
% 2.87/1.46  Main loop            : 0.42
% 2.87/1.46  Inferencing          : 0.18
% 2.87/1.46  Reduction            : 0.14
% 2.87/1.46  Demodulation         : 0.12
% 2.87/1.46  BG Simplification    : 0.02
% 2.87/1.46  Subsumption          : 0.06
% 2.87/1.46  Abstraction          : 0.02
% 2.87/1.46  MUC search           : 0.00
% 2.87/1.46  Cooper               : 0.00
% 2.87/1.46  Total                : 0.72
% 2.87/1.46  Index Insertion      : 0.00
% 2.87/1.46  Index Deletion       : 0.00
% 2.87/1.46  Index Matching       : 0.00
% 2.87/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

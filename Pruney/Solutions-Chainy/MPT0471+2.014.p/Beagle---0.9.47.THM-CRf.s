%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:22 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   36 (  37 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_30,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_18,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_50,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = k2_xboole_0(k1_xboole_0,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_6,plain,(
    ! [A_2] : k5_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_97,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_6])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    ! [A_12] :
      ( k2_xboole_0(k1_relat_1(A_12),k2_relat_1(A_12)) = k3_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_78,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16,c_71])).

tff(c_113,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_78])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:25:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.08  %$ v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0
% 1.67/1.08  
% 1.67/1.08  %Foreground sorts:
% 1.67/1.08  
% 1.67/1.08  
% 1.67/1.08  %Background operators:
% 1.67/1.08  
% 1.67/1.08  
% 1.67/1.08  %Foreground operators:
% 1.67/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.08  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.67/1.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.67/1.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.08  
% 1.67/1.09  tff(f_45, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 1.67/1.09  tff(f_28, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.67/1.09  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.67/1.09  tff(f_30, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.67/1.09  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.67/1.09  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.67/1.09  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.67/1.09  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.67/1.09  tff(c_18, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.09  tff(c_4, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.67/1.09  tff(c_50, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.09  tff(c_86, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=k2_xboole_0(k1_xboole_0, A_13))), inference(superposition, [status(thm), theory('equality')], [c_4, c_50])).
% 1.67/1.09  tff(c_6, plain, (![A_2]: (k5_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.67/1.09  tff(c_97, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_86, c_6])).
% 1.67/1.09  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.67/1.09  tff(c_36, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.67/1.09  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 1.67/1.09  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.09  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.09  tff(c_62, plain, (![A_12]: (k2_xboole_0(k1_relat_1(A_12), k2_relat_1(A_12))=k3_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.09  tff(c_71, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_62])).
% 1.67/1.09  tff(c_78, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k3_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16, c_71])).
% 1.67/1.09  tff(c_113, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_97, c_78])).
% 1.67/1.09  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_113])).
% 1.67/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  Inference rules
% 1.67/1.09  ----------------------
% 1.67/1.09  #Ref     : 0
% 1.67/1.09  #Sup     : 24
% 1.67/1.09  #Fact    : 0
% 1.67/1.09  #Define  : 0
% 1.67/1.09  #Split   : 0
% 1.67/1.09  #Chain   : 0
% 1.67/1.09  #Close   : 0
% 1.67/1.09  
% 1.67/1.09  Ordering : KBO
% 1.67/1.09  
% 1.67/1.09  Simplification rules
% 1.67/1.09  ----------------------
% 1.67/1.09  #Subsume      : 0
% 1.67/1.09  #Demod        : 8
% 1.67/1.09  #Tautology    : 19
% 1.67/1.09  #SimpNegUnit  : 1
% 1.67/1.09  #BackRed      : 1
% 1.67/1.09  
% 1.67/1.09  #Partial instantiations: 0
% 1.67/1.09  #Strategies tried      : 1
% 1.67/1.09  
% 1.67/1.09  Timing (in seconds)
% 1.67/1.09  ----------------------
% 1.67/1.09  Preprocessing        : 0.24
% 1.67/1.09  Parsing              : 0.14
% 1.67/1.09  CNF conversion       : 0.01
% 1.67/1.09  Main loop            : 0.10
% 1.67/1.09  Inferencing          : 0.05
% 1.67/1.09  Reduction            : 0.03
% 1.67/1.10  Demodulation         : 0.02
% 1.67/1.10  BG Simplification    : 0.01
% 1.67/1.10  Subsumption          : 0.01
% 1.67/1.10  Abstraction          : 0.00
% 1.67/1.10  MUC search           : 0.00
% 1.67/1.10  Cooper               : 0.00
% 1.67/1.10  Total                : 0.37
% 1.67/1.10  Index Insertion      : 0.00
% 1.67/1.10  Index Deletion       : 0.00
% 1.67/1.10  Index Matching       : 0.00
% 1.67/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

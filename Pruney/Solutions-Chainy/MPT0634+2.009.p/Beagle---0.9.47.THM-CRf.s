%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:20 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  32 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [B_11,A_12] :
      ( k3_xboole_0(k1_relat_1(B_11),A_12) = k1_relat_1(k7_relat_1(B_11,A_12))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,k1_relat_1(B_14)) = k1_relat_1(k7_relat_1(B_14,A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_47,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_53,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_13])).

tff(c_59,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_90,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_59])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:18:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  %$ v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.63/1.10  
% 1.63/1.10  %Foreground sorts:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Background operators:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Foreground operators:
% 1.63/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.63/1.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.63/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.63/1.10  
% 1.63/1.11  tff(f_42, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 1.63/1.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.63/1.11  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.63/1.11  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.63/1.11  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.11  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.11  tff(c_61, plain, (![B_11, A_12]: (k3_xboole_0(k1_relat_1(B_11), A_12)=k1_relat_1(k7_relat_1(B_11, A_12)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.11  tff(c_84, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k1_relat_1(B_14))=k1_relat_1(k7_relat_1(B_14, A_13)) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 1.63/1.11  tff(c_47, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.11  tff(c_8, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.11  tff(c_13, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 1.63/1.11  tff(c_53, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_47, c_13])).
% 1.63/1.11  tff(c_59, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_53])).
% 1.63/1.11  tff(c_90, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_59])).
% 1.63/1.11  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_90])).
% 1.63/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  Inference rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Ref     : 0
% 1.63/1.11  #Sup     : 26
% 1.63/1.11  #Fact    : 0
% 1.63/1.11  #Define  : 0
% 1.63/1.11  #Split   : 0
% 1.63/1.11  #Chain   : 0
% 1.63/1.11  #Close   : 0
% 1.63/1.11  
% 1.63/1.11  Ordering : KBO
% 1.63/1.11  
% 1.63/1.11  Simplification rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Subsume      : 0
% 1.63/1.11  #Demod        : 3
% 1.63/1.11  #Tautology    : 13
% 1.63/1.11  #SimpNegUnit  : 0
% 1.63/1.11  #BackRed      : 0
% 1.63/1.11  
% 1.63/1.11  #Partial instantiations: 0
% 1.63/1.11  #Strategies tried      : 1
% 1.63/1.11  
% 1.63/1.11  Timing (in seconds)
% 1.63/1.11  ----------------------
% 1.63/1.11  Preprocessing        : 0.26
% 1.63/1.11  Parsing              : 0.14
% 1.63/1.11  CNF conversion       : 0.01
% 1.63/1.11  Main loop            : 0.09
% 1.63/1.11  Inferencing          : 0.04
% 1.63/1.11  Reduction            : 0.03
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.01
% 1.63/1.11  Abstraction          : 0.01
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.37
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

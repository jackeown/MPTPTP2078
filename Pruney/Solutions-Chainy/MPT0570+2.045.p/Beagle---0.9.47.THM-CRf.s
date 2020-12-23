%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:47 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(k2_relat_1(B_25),A_26)
      | k10_relat_1(B_25,A_26) != k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,k2_relat_1(B_28))
      | k10_relat_1(B_28,A_27) != k1_xboole_0
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,k2_relat_1(B_34)) = A_33
      | k10_relat_1(B_34,A_33) != k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    k4_xboole_0('#skF_1',k2_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_36])).

tff(c_132,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_120])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:00:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.14  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.14  
% 1.60/1.14  %Foreground sorts:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Background operators:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Foreground operators:
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.60/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.14  
% 1.60/1.15  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 1.60/1.15  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.60/1.15  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.60/1.15  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.60/1.15  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.60/1.15  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.15  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.15  tff(c_16, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.15  tff(c_73, plain, (![B_25, A_26]: (r1_xboole_0(k2_relat_1(B_25), A_26) | k10_relat_1(B_25, A_26)!=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.15  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.15  tff(c_85, plain, (![A_27, B_28]: (r1_xboole_0(A_27, k2_relat_1(B_28)) | k10_relat_1(B_28, A_27)!=k1_xboole_0 | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_73, c_2])).
% 1.60/1.15  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.15  tff(c_105, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_relat_1(B_34))=A_33 | k10_relat_1(B_34, A_33)!=k1_xboole_0 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_85, c_8])).
% 1.60/1.15  tff(c_18, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.60/1.15  tff(c_32, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.15  tff(c_36, plain, (k4_xboole_0('#skF_1', k2_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_32])).
% 1.60/1.15  tff(c_120, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_105, c_36])).
% 1.60/1.15  tff(c_132, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_120])).
% 1.60/1.15  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_132])).
% 1.60/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  Inference rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Ref     : 0
% 1.60/1.15  #Sup     : 27
% 1.60/1.15  #Fact    : 0
% 1.60/1.15  #Define  : 0
% 1.60/1.15  #Split   : 0
% 1.60/1.15  #Chain   : 0
% 1.60/1.15  #Close   : 0
% 1.60/1.15  
% 1.60/1.15  Ordering : KBO
% 1.60/1.15  
% 1.60/1.15  Simplification rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Subsume      : 4
% 1.60/1.15  #Demod        : 4
% 1.60/1.15  #Tautology    : 9
% 1.60/1.15  #SimpNegUnit  : 1
% 1.60/1.15  #BackRed      : 0
% 1.60/1.15  
% 1.60/1.15  #Partial instantiations: 0
% 1.60/1.15  #Strategies tried      : 1
% 1.60/1.15  
% 1.60/1.15  Timing (in seconds)
% 1.60/1.15  ----------------------
% 1.77/1.15  Preprocessing        : 0.26
% 1.77/1.15  Parsing              : 0.14
% 1.77/1.15  CNF conversion       : 0.02
% 1.77/1.15  Main loop            : 0.12
% 1.77/1.15  Inferencing          : 0.05
% 1.77/1.15  Reduction            : 0.03
% 1.77/1.15  Demodulation         : 0.02
% 1.77/1.15  BG Simplification    : 0.01
% 1.77/1.15  Subsumption          : 0.02
% 1.77/1.15  Abstraction          : 0.01
% 1.77/1.15  MUC search           : 0.00
% 1.77/1.15  Cooper               : 0.00
% 1.77/1.15  Total                : 0.41
% 1.77/1.15  Index Insertion      : 0.00
% 1.77/1.15  Index Deletion       : 0.00
% 1.77/1.15  Index Matching       : 0.00
% 1.77/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

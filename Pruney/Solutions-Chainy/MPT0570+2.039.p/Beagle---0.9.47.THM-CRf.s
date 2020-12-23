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
% DateTime   : Thu Dec  3 10:01:46 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
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
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(k2_relat_1(B_23),A_24)
      | k10_relat_1(B_23,A_24) != k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,k2_relat_1(B_26))
      | k10_relat_1(B_26,A_25) != k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_66,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,k2_relat_1(B_32)) = k1_xboole_0
      | k10_relat_1(B_32,A_31) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_30])).

tff(c_124,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_34])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_124])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.75/1.15  
% 1.75/1.15  %Foreground sorts:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Background operators:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Foreground operators:
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.75/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.75/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.75/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.15  
% 1.75/1.16  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 1.75/1.16  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.75/1.16  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.75/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.75/1.16  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.75/1.16  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.16  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.16  tff(c_14, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.16  tff(c_66, plain, (![B_23, A_24]: (r1_xboole_0(k2_relat_1(B_23), A_24) | k10_relat_1(B_23, A_24)!=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.16  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.16  tff(c_78, plain, (![A_25, B_26]: (r1_xboole_0(A_25, k2_relat_1(B_26)) | k10_relat_1(B_26, A_25)!=k1_xboole_0 | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_66, c_6])).
% 1.75/1.16  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.16  tff(c_108, plain, (![A_31, B_32]: (k3_xboole_0(A_31, k2_relat_1(B_32))=k1_xboole_0 | k10_relat_1(B_32, A_31)!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_78, c_2])).
% 1.75/1.16  tff(c_16, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.16  tff(c_30, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.16  tff(c_34, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_16, c_30])).
% 1.75/1.16  tff(c_124, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_108, c_34])).
% 1.75/1.16  tff(c_140, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_124])).
% 1.75/1.16  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_140])).
% 1.75/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  Inference rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Ref     : 0
% 1.75/1.16  #Sup     : 30
% 1.75/1.16  #Fact    : 0
% 1.75/1.16  #Define  : 0
% 1.75/1.16  #Split   : 0
% 1.75/1.16  #Chain   : 0
% 1.75/1.16  #Close   : 0
% 1.75/1.16  
% 1.75/1.16  Ordering : KBO
% 1.75/1.16  
% 1.75/1.16  Simplification rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Subsume      : 4
% 1.75/1.16  #Demod        : 2
% 1.75/1.16  #Tautology    : 11
% 1.75/1.16  #SimpNegUnit  : 1
% 1.75/1.16  #BackRed      : 0
% 1.75/1.16  
% 1.75/1.16  #Partial instantiations: 0
% 1.75/1.16  #Strategies tried      : 1
% 1.75/1.16  
% 1.75/1.16  Timing (in seconds)
% 1.75/1.16  ----------------------
% 1.75/1.17  Preprocessing        : 0.27
% 1.75/1.17  Parsing              : 0.15
% 1.75/1.17  CNF conversion       : 0.02
% 1.75/1.17  Main loop            : 0.13
% 1.75/1.17  Inferencing          : 0.06
% 1.75/1.17  Reduction            : 0.03
% 1.75/1.17  Demodulation         : 0.02
% 1.75/1.17  BG Simplification    : 0.01
% 1.75/1.17  Subsumption          : 0.02
% 1.75/1.17  Abstraction          : 0.01
% 1.75/1.17  MUC search           : 0.00
% 1.75/1.17  Cooper               : 0.00
% 1.75/1.17  Total                : 0.43
% 1.75/1.17  Index Insertion      : 0.00
% 1.75/1.17  Index Deletion       : 0.00
% 1.75/1.17  Index Matching       : 0.00
% 1.75/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

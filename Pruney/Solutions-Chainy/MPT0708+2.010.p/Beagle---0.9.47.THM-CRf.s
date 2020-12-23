%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:24 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  60 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(A,k1_relat_1(C))
            & r1_tarski(k9_relat_1(C,A),B) )
         => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k10_relat_1(C_8,A_6),k10_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,k10_relat_1(B_25,k9_relat_1(B_25,A_24)))
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_388,plain,(
    ! [A_68,B_69] :
      ( k2_xboole_0(A_68,k10_relat_1(B_69,k9_relat_1(B_69,A_68))) = k10_relat_1(B_69,k9_relat_1(B_69,A_68))
      | ~ r1_tarski(A_68,k1_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_89,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_443,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(k10_relat_1(B_72,k9_relat_1(B_72,A_70)),C_71)
      | ~ r1_tarski(A_70,k1_relat_1(B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_2])).

tff(c_689,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(A_87,k10_relat_1(C_88,B_89))
      | ~ r1_tarski(A_87,k1_relat_1(C_88))
      | ~ r1_tarski(k9_relat_1(C_88,A_87),B_89)
      | ~ v1_relat_1(C_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_443])).

tff(c_713,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_689])).

tff(c_728,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_713])).

tff(c_730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.55  
% 3.06/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.55  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.55  
% 3.06/1.55  %Foreground sorts:
% 3.06/1.55  
% 3.06/1.55  
% 3.06/1.55  %Background operators:
% 3.06/1.55  
% 3.06/1.55  
% 3.06/1.55  %Foreground operators:
% 3.06/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.06/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.06/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.55  
% 3.06/1.56  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.06/1.56  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 3.06/1.56  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.06/1.56  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.06/1.56  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.06/1.56  tff(c_10, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.56  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.56  tff(c_14, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.56  tff(c_12, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.56  tff(c_6, plain, (![C_8, A_6, B_7]: (r1_tarski(k10_relat_1(C_8, A_6), k10_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.06/1.56  tff(c_89, plain, (![A_24, B_25]: (r1_tarski(A_24, k10_relat_1(B_25, k9_relat_1(B_25, A_24))) | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.06/1.56  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.56  tff(c_388, plain, (![A_68, B_69]: (k2_xboole_0(A_68, k10_relat_1(B_69, k9_relat_1(B_69, A_68)))=k10_relat_1(B_69, k9_relat_1(B_69, A_68)) | ~r1_tarski(A_68, k1_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_89, c_4])).
% 3.06/1.56  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.56  tff(c_443, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(k10_relat_1(B_72, k9_relat_1(B_72, A_70)), C_71) | ~r1_tarski(A_70, k1_relat_1(B_72)) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_388, c_2])).
% 3.06/1.56  tff(c_689, plain, (![A_87, C_88, B_89]: (r1_tarski(A_87, k10_relat_1(C_88, B_89)) | ~r1_tarski(A_87, k1_relat_1(C_88)) | ~r1_tarski(k9_relat_1(C_88, A_87), B_89) | ~v1_relat_1(C_88))), inference(resolution, [status(thm)], [c_6, c_443])).
% 3.06/1.56  tff(c_713, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_689])).
% 3.06/1.56  tff(c_728, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_713])).
% 3.06/1.56  tff(c_730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_728])).
% 3.06/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.56  
% 3.06/1.56  Inference rules
% 3.06/1.56  ----------------------
% 3.06/1.56  #Ref     : 0
% 3.06/1.56  #Sup     : 174
% 3.06/1.56  #Fact    : 0
% 3.06/1.56  #Define  : 0
% 3.06/1.56  #Split   : 3
% 3.06/1.56  #Chain   : 0
% 3.06/1.56  #Close   : 0
% 3.06/1.56  
% 3.06/1.56  Ordering : KBO
% 3.06/1.56  
% 3.06/1.56  Simplification rules
% 3.06/1.56  ----------------------
% 3.06/1.56  #Subsume      : 19
% 3.06/1.56  #Demod        : 24
% 3.06/1.56  #Tautology    : 31
% 3.06/1.56  #SimpNegUnit  : 1
% 3.06/1.56  #BackRed      : 0
% 3.06/1.56  
% 3.06/1.56  #Partial instantiations: 0
% 3.06/1.56  #Strategies tried      : 1
% 3.06/1.56  
% 3.06/1.56  Timing (in seconds)
% 3.06/1.56  ----------------------
% 3.06/1.56  Preprocessing        : 0.29
% 3.06/1.56  Parsing              : 0.16
% 3.06/1.56  CNF conversion       : 0.02
% 3.06/1.56  Main loop            : 0.40
% 3.06/1.56  Inferencing          : 0.15
% 3.06/1.56  Reduction            : 0.10
% 3.06/1.56  Demodulation         : 0.07
% 3.06/1.56  BG Simplification    : 0.02
% 3.06/1.56  Subsumption          : 0.10
% 3.06/1.56  Abstraction          : 0.02
% 3.06/1.56  MUC search           : 0.00
% 3.06/1.56  Cooper               : 0.00
% 3.06/1.56  Total                : 0.72
% 3.06/1.57  Index Insertion      : 0.00
% 3.06/1.57  Index Deletion       : 0.00
% 3.06/1.57  Index Matching       : 0.00
% 3.06/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

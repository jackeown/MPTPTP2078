%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:16 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   36 (  55 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 ( 119 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k10_relat_1(C,A) = k10_relat_1(C,B)
            & r1_tarski(A,k2_relat_1(C))
            & r1_tarski(B,k2_relat_1(C)) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(c_8,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_23,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_10,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_23])).

tff(c_14,plain,(
    k10_relat_1('#skF_3','#skF_2') = k10_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,k9_relat_1(B_10,k1_relat_1(B_10))) = k9_relat_1(B_10,k10_relat_1(B_10,A_9))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [A_11,A_12] :
      ( k9_relat_1(A_11,k10_relat_1(A_11,A_12)) = k3_xboole_0(A_12,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_49])).

tff(c_70,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_61])).

tff(c_74,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_16,c_30,c_70])).

tff(c_58,plain,(
    ! [A_3,A_9] :
      ( k9_relat_1(A_3,k10_relat_1(A_3,A_9)) = k3_xboole_0(A_9,k2_relat_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_49])).

tff(c_78,plain,
    ( k3_xboole_0('#skF_1',k2_relat_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_58])).

tff(c_85,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_16,c_31,c_78])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.25  
% 1.90/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.25  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.25  
% 1.90/1.25  %Foreground sorts:
% 1.90/1.25  
% 1.90/1.25  
% 1.90/1.25  %Background operators:
% 1.90/1.25  
% 1.90/1.25  
% 1.90/1.25  %Foreground operators:
% 1.90/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.90/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.90/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.25  
% 1.90/1.26  tff(f_52, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k10_relat_1(C, A) = k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) & r1_tarski(B, k2_relat_1(C))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_funct_1)).
% 1.90/1.26  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.90/1.26  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.90/1.26  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 1.90/1.26  tff(c_8, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.26  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.26  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.26  tff(c_12, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.26  tff(c_23, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.26  tff(c_31, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.90/1.26  tff(c_10, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.26  tff(c_30, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_10, c_23])).
% 1.90/1.26  tff(c_14, plain, (k10_relat_1('#skF_3', '#skF_2')=k10_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.26  tff(c_4, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.26  tff(c_49, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k9_relat_1(B_10, k1_relat_1(B_10)))=k9_relat_1(B_10, k10_relat_1(B_10, A_9)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.26  tff(c_61, plain, (![A_11, A_12]: (k9_relat_1(A_11, k10_relat_1(A_11, A_12))=k3_xboole_0(A_12, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_4, c_49])).
% 1.90/1.26  tff(c_70, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_2', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_61])).
% 1.90/1.26  tff(c_74, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_16, c_30, c_70])).
% 1.90/1.26  tff(c_58, plain, (![A_3, A_9]: (k9_relat_1(A_3, k10_relat_1(A_3, A_9))=k3_xboole_0(A_9, k2_relat_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_49])).
% 1.90/1.26  tff(c_78, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_3'))='#skF_2' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_74, c_58])).
% 1.90/1.26  tff(c_85, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_16, c_31, c_78])).
% 1.90/1.26  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_85])).
% 1.90/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.26  
% 1.90/1.26  Inference rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Ref     : 0
% 1.90/1.26  #Sup     : 20
% 1.90/1.26  #Fact    : 0
% 1.90/1.26  #Define  : 0
% 1.90/1.26  #Split   : 0
% 1.90/1.26  #Chain   : 0
% 1.90/1.26  #Close   : 0
% 1.90/1.26  
% 1.90/1.26  Ordering : KBO
% 1.90/1.26  
% 1.90/1.26  Simplification rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Subsume      : 0
% 1.90/1.26  #Demod        : 8
% 1.90/1.26  #Tautology    : 13
% 1.90/1.26  #SimpNegUnit  : 1
% 1.90/1.26  #BackRed      : 0
% 1.90/1.26  
% 1.90/1.26  #Partial instantiations: 0
% 1.90/1.26  #Strategies tried      : 1
% 1.90/1.26  
% 1.90/1.26  Timing (in seconds)
% 1.90/1.26  ----------------------
% 1.90/1.26  Preprocessing        : 0.35
% 1.90/1.26  Parsing              : 0.19
% 1.90/1.26  CNF conversion       : 0.02
% 1.90/1.26  Main loop            : 0.11
% 1.90/1.26  Inferencing          : 0.05
% 1.90/1.26  Reduction            : 0.03
% 1.90/1.26  Demodulation         : 0.03
% 1.90/1.26  BG Simplification    : 0.01
% 1.90/1.26  Subsumption          : 0.01
% 1.90/1.26  Abstraction          : 0.01
% 1.90/1.26  MUC search           : 0.00
% 1.90/1.26  Cooper               : 0.00
% 1.90/1.26  Total                : 0.49
% 1.90/1.26  Index Insertion      : 0.00
% 1.90/1.26  Index Deletion       : 0.00
% 1.90/1.26  Index Matching       : 0.00
% 1.90/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

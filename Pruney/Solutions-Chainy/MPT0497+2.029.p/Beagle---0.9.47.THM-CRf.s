%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:43 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  87 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_84,plain,(
    ! [B_20,A_21] :
      ( k3_xboole_0(k1_relat_1(B_20),A_21) = k1_relat_1(k7_relat_1(B_20,A_21))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_90,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_62])).

tff(c_102,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_90])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k7_relat_1(A_22,B_23)) != k1_xboole_0
      | k7_relat_1(A_22,B_23) = k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_118,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_115])).

tff(c_121,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_118])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_121])).

tff(c_124,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_170,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(k1_relat_1(B_27),A_28) = k1_relat_1(k7_relat_1(B_27,A_28))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_125,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_149,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_125])).

tff(c_176,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_149])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12,c_124,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.16  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.80/1.16  
% 1.80/1.16  %Foreground sorts:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Background operators:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Foreground operators:
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.80/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.80/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.80/1.16  
% 1.80/1.17  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.80/1.17  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.80/1.17  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.80/1.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.80/1.17  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.80/1.17  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.80/1.17  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.17  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.17  tff(c_28, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.17  tff(c_58, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 1.80/1.17  tff(c_22, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.17  tff(c_83, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 1.80/1.17  tff(c_84, plain, (![B_20, A_21]: (k3_xboole_0(k1_relat_1(B_20), A_21)=k1_relat_1(k7_relat_1(B_20, A_21)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.17  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.17  tff(c_62, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.80/1.17  tff(c_90, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_62])).
% 1.80/1.17  tff(c_102, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_90])).
% 1.80/1.17  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.17  tff(c_38, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.17  tff(c_115, plain, (![A_22, B_23]: (k1_relat_1(k7_relat_1(A_22, B_23))!=k1_xboole_0 | k7_relat_1(A_22, B_23)=k1_xboole_0 | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_8, c_38])).
% 1.80/1.17  tff(c_118, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102, c_115])).
% 1.80/1.17  tff(c_121, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_118])).
% 1.80/1.17  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_121])).
% 1.80/1.17  tff(c_124, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 1.80/1.17  tff(c_170, plain, (![B_27, A_28]: (k3_xboole_0(k1_relat_1(B_27), A_28)=k1_relat_1(k7_relat_1(B_27, A_28)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.17  tff(c_142, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.17  tff(c_125, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 1.80/1.17  tff(c_149, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_125])).
% 1.80/1.17  tff(c_176, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_170, c_149])).
% 1.80/1.17  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_12, c_124, c_176])).
% 1.80/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  Inference rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Ref     : 0
% 1.80/1.17  #Sup     : 36
% 1.80/1.17  #Fact    : 0
% 1.80/1.17  #Define  : 0
% 1.80/1.17  #Split   : 5
% 1.80/1.17  #Chain   : 0
% 1.80/1.17  #Close   : 0
% 1.80/1.17  
% 1.80/1.17  Ordering : KBO
% 1.80/1.17  
% 1.80/1.17  Simplification rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Subsume      : 1
% 1.80/1.17  #Demod        : 12
% 1.80/1.17  #Tautology    : 22
% 1.80/1.17  #SimpNegUnit  : 1
% 1.80/1.17  #BackRed      : 0
% 1.80/1.17  
% 1.80/1.17  #Partial instantiations: 0
% 1.80/1.17  #Strategies tried      : 1
% 1.80/1.17  
% 1.80/1.17  Timing (in seconds)
% 1.80/1.17  ----------------------
% 1.80/1.17  Preprocessing        : 0.27
% 1.80/1.17  Parsing              : 0.14
% 1.89/1.17  CNF conversion       : 0.02
% 1.89/1.17  Main loop            : 0.14
% 1.89/1.17  Inferencing          : 0.05
% 1.89/1.17  Reduction            : 0.04
% 1.89/1.17  Demodulation         : 0.03
% 1.89/1.17  BG Simplification    : 0.01
% 1.89/1.17  Subsumption          : 0.03
% 1.89/1.17  Abstraction          : 0.01
% 1.89/1.17  MUC search           : 0.00
% 1.89/1.17  Cooper               : 0.00
% 1.89/1.17  Total                : 0.44
% 1.89/1.17  Index Insertion      : 0.00
% 1.89/1.17  Index Deletion       : 0.00
% 1.89/1.17  Index Matching       : 0.00
% 1.89/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

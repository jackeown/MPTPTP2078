%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:11 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  55 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( k1_relat_1(A) = k1_relat_1(B)
                 => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    k1_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_17,plain,(
    ! [A_8,B_9] :
      ( k10_relat_1(A_8,k1_relat_1(B_9)) = k1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k1_relat_1('#skF_1')) = k1_relat_1(k5_relat_1(A_8,'#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_17])).

tff(c_31,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k1_relat_1('#skF_1')) = k1_relat_1(k5_relat_1(A_10,'#skF_2'))
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k10_relat_1(A_1,k1_relat_1(B_3)) = k1_relat_1(k5_relat_1(A_1,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_10] :
      ( k1_relat_1(k5_relat_1(A_10,'#skF_2')) = k1_relat_1(k5_relat_1(A_10,'#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_2])).

tff(c_51,plain,(
    ! [A_11] :
      ( k1_relat_1(k5_relat_1(A_11,'#skF_2')) = k1_relat_1(k5_relat_1(A_11,'#skF_1'))
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_37])).

tff(c_4,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1(k5_relat_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_4])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.09  
% 1.59/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.09  %$ v1_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.59/1.09  
% 1.59/1.09  %Foreground sorts:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Background operators:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Foreground operators:
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.59/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.59/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.59/1.09  
% 1.59/1.10  tff(f_45, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 1.59/1.10  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 1.59/1.10  tff(c_8, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.10  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.10  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.10  tff(c_6, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.10  tff(c_17, plain, (![A_8, B_9]: (k10_relat_1(A_8, k1_relat_1(B_9))=k1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.59/1.10  tff(c_26, plain, (![A_8]: (k10_relat_1(A_8, k1_relat_1('#skF_1'))=k1_relat_1(k5_relat_1(A_8, '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_6, c_17])).
% 1.59/1.10  tff(c_31, plain, (![A_10]: (k10_relat_1(A_10, k1_relat_1('#skF_1'))=k1_relat_1(k5_relat_1(A_10, '#skF_2')) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 1.59/1.10  tff(c_2, plain, (![A_1, B_3]: (k10_relat_1(A_1, k1_relat_1(B_3))=k1_relat_1(k5_relat_1(A_1, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.59/1.10  tff(c_37, plain, (![A_10]: (k1_relat_1(k5_relat_1(A_10, '#skF_2'))=k1_relat_1(k5_relat_1(A_10, '#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_31, c_2])).
% 1.59/1.10  tff(c_51, plain, (![A_11]: (k1_relat_1(k5_relat_1(A_11, '#skF_2'))=k1_relat_1(k5_relat_1(A_11, '#skF_1')) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_37])).
% 1.59/1.10  tff(c_4, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1(k5_relat_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.10  tff(c_60, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_51, c_4])).
% 1.59/1.10  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_60])).
% 1.59/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  Inference rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Ref     : 0
% 1.59/1.10  #Sup     : 13
% 1.59/1.10  #Fact    : 0
% 1.59/1.10  #Define  : 0
% 1.59/1.10  #Split   : 0
% 1.59/1.10  #Chain   : 0
% 1.59/1.10  #Close   : 0
% 1.59/1.10  
% 1.59/1.10  Ordering : KBO
% 1.59/1.10  
% 1.59/1.10  Simplification rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Subsume      : 0
% 1.59/1.10  #Demod        : 4
% 1.59/1.10  #Tautology    : 7
% 1.59/1.10  #SimpNegUnit  : 0
% 1.59/1.10  #BackRed      : 0
% 1.59/1.10  
% 1.59/1.10  #Partial instantiations: 0
% 1.59/1.10  #Strategies tried      : 1
% 1.59/1.10  
% 1.59/1.10  Timing (in seconds)
% 1.59/1.10  ----------------------
% 1.59/1.10  Preprocessing        : 0.26
% 1.59/1.10  Parsing              : 0.14
% 1.59/1.10  CNF conversion       : 0.02
% 1.59/1.10  Main loop            : 0.08
% 1.59/1.10  Inferencing          : 0.04
% 1.59/1.10  Reduction            : 0.02
% 1.59/1.10  Demodulation         : 0.02
% 1.59/1.10  BG Simplification    : 0.01
% 1.59/1.10  Subsumption          : 0.01
% 1.59/1.10  Abstraction          : 0.01
% 1.59/1.10  MUC search           : 0.00
% 1.59/1.10  Cooper               : 0.00
% 1.59/1.10  Total                : 0.37
% 1.59/1.10  Index Insertion      : 0.00
% 1.59/1.10  Index Deletion       : 0.00
% 1.59/1.10  Index Matching       : 0.00
% 1.59/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

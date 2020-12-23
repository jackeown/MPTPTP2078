%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:11 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.62s
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
%$ v1_relat_1 > k9_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_45,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( k2_relat_1(A) = k2_relat_1(B)
                 => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

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
    k2_relat_1('#skF_2') = k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_17,plain,(
    ! [B_8,A_9] :
      ( k9_relat_1(B_8,k2_relat_1(A_9)) = k2_relat_1(k5_relat_1(A_9,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [B_8] :
      ( k9_relat_1(B_8,k2_relat_1('#skF_1')) = k2_relat_1(k5_relat_1('#skF_2',B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_17])).

tff(c_31,plain,(
    ! [B_10] :
      ( k9_relat_1(B_10,k2_relat_1('#skF_1')) = k2_relat_1(k5_relat_1('#skF_2',B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( k9_relat_1(B_3,k2_relat_1(A_1)) = k2_relat_1(k5_relat_1(A_1,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [B_10] :
      ( k2_relat_1(k5_relat_1('#skF_2',B_10)) = k2_relat_1(k5_relat_1('#skF_1',B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_2])).

tff(c_51,plain,(
    ! [B_11] :
      ( k2_relat_1(k5_relat_1('#skF_2',B_11)) = k2_relat_1(k5_relat_1('#skF_1',B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_37])).

tff(c_4,plain,(
    k2_relat_1(k5_relat_1('#skF_2','#skF_3')) != k2_relat_1(k5_relat_1('#skF_1','#skF_3')) ),
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
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:34:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.07  
% 1.49/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.08  %$ v1_relat_1 > k9_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.49/1.08  
% 1.49/1.08  %Foreground sorts:
% 1.49/1.08  
% 1.49/1.08  
% 1.49/1.08  %Background operators:
% 1.49/1.08  
% 1.49/1.08  
% 1.49/1.08  %Foreground operators:
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.49/1.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.49/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.49/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.49/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.49/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.08  
% 1.62/1.08  tff(f_45, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 1.62/1.08  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.62/1.08  tff(c_8, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.08  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.08  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.08  tff(c_6, plain, (k2_relat_1('#skF_2')=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.08  tff(c_17, plain, (![B_8, A_9]: (k9_relat_1(B_8, k2_relat_1(A_9))=k2_relat_1(k5_relat_1(A_9, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.08  tff(c_26, plain, (![B_8]: (k9_relat_1(B_8, k2_relat_1('#skF_1'))=k2_relat_1(k5_relat_1('#skF_2', B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_17])).
% 1.62/1.08  tff(c_31, plain, (![B_10]: (k9_relat_1(B_10, k2_relat_1('#skF_1'))=k2_relat_1(k5_relat_1('#skF_2', B_10)) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 1.62/1.08  tff(c_2, plain, (![B_3, A_1]: (k9_relat_1(B_3, k2_relat_1(A_1))=k2_relat_1(k5_relat_1(A_1, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.08  tff(c_37, plain, (![B_10]: (k2_relat_1(k5_relat_1('#skF_2', B_10))=k2_relat_1(k5_relat_1('#skF_1', B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1('#skF_1') | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_31, c_2])).
% 1.62/1.08  tff(c_51, plain, (![B_11]: (k2_relat_1(k5_relat_1('#skF_2', B_11))=k2_relat_1(k5_relat_1('#skF_1', B_11)) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_37])).
% 1.62/1.08  tff(c_4, plain, (k2_relat_1(k5_relat_1('#skF_2', '#skF_3'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.08  tff(c_60, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_51, c_4])).
% 1.62/1.08  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_60])).
% 1.62/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  Inference rules
% 1.62/1.08  ----------------------
% 1.62/1.08  #Ref     : 0
% 1.62/1.08  #Sup     : 13
% 1.62/1.08  #Fact    : 0
% 1.62/1.08  #Define  : 0
% 1.62/1.08  #Split   : 0
% 1.62/1.08  #Chain   : 0
% 1.62/1.08  #Close   : 0
% 1.62/1.08  
% 1.62/1.08  Ordering : KBO
% 1.62/1.08  
% 1.62/1.08  Simplification rules
% 1.62/1.08  ----------------------
% 1.62/1.08  #Subsume      : 0
% 1.62/1.08  #Demod        : 4
% 1.62/1.08  #Tautology    : 7
% 1.62/1.08  #SimpNegUnit  : 0
% 1.62/1.08  #BackRed      : 0
% 1.62/1.08  
% 1.62/1.08  #Partial instantiations: 0
% 1.62/1.08  #Strategies tried      : 1
% 1.62/1.08  
% 1.62/1.08  Timing (in seconds)
% 1.62/1.08  ----------------------
% 1.62/1.09  Preprocessing        : 0.26
% 1.62/1.09  Parsing              : 0.13
% 1.62/1.09  CNF conversion       : 0.02
% 1.62/1.09  Main loop            : 0.08
% 1.62/1.09  Inferencing          : 0.04
% 1.62/1.09  Reduction            : 0.02
% 1.62/1.09  Demodulation         : 0.02
% 1.62/1.09  BG Simplification    : 0.01
% 1.62/1.09  Subsumption          : 0.01
% 1.62/1.09  Abstraction          : 0.01
% 1.62/1.09  MUC search           : 0.00
% 1.62/1.09  Cooper               : 0.00
% 1.62/1.09  Total                : 0.36
% 1.62/1.09  Index Insertion      : 0.00
% 1.62/1.09  Index Deletion       : 0.00
% 1.62/1.09  Index Matching       : 0.00
% 1.62/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

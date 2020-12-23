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
% DateTime   : Thu Dec  3 10:00:11 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_38,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [B_5,A_6] :
      ( k5_relat_1(B_5,k6_relat_1(A_6)) = k8_relat_1(A_6,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k6_relat_1(k2_relat_1(A_3))) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [B_7] :
      ( k8_relat_1(k2_relat_1(B_7),B_7) = B_7
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4])).

tff(c_6,plain,(
    k8_relat_1(k2_relat_1('#skF_1'),'#skF_1') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_48,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.36  
% 1.83/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.38  %$ v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_1
% 1.93/1.38  
% 1.93/1.38  %Foreground sorts:
% 1.93/1.38  
% 1.93/1.38  
% 1.93/1.38  %Background operators:
% 1.93/1.38  
% 1.93/1.38  
% 1.93/1.38  %Foreground operators:
% 1.93/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.93/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.93/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.38  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.38  
% 1.93/1.39  tff(f_38, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 1.93/1.39  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.93/1.39  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 1.93/1.39  tff(c_8, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.39  tff(c_18, plain, (![B_5, A_6]: (k5_relat_1(B_5, k6_relat_1(A_6))=k8_relat_1(A_6, B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.39  tff(c_4, plain, (![A_3]: (k5_relat_1(A_3, k6_relat_1(k2_relat_1(A_3)))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.39  tff(c_34, plain, (![B_7]: (k8_relat_1(k2_relat_1(B_7), B_7)=B_7 | ~v1_relat_1(B_7) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4])).
% 1.93/1.39  tff(c_6, plain, (k8_relat_1(k2_relat_1('#skF_1'), '#skF_1')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.39  tff(c_40, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_6])).
% 1.93/1.39  tff(c_48, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_40])).
% 1.93/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.39  
% 1.93/1.39  Inference rules
% 1.93/1.39  ----------------------
% 1.93/1.39  #Ref     : 0
% 1.93/1.39  #Sup     : 9
% 1.93/1.39  #Fact    : 0
% 1.93/1.39  #Define  : 0
% 1.93/1.39  #Split   : 0
% 1.93/1.39  #Chain   : 0
% 1.93/1.39  #Close   : 0
% 1.93/1.39  
% 1.93/1.39  Ordering : KBO
% 1.93/1.39  
% 1.93/1.39  Simplification rules
% 1.93/1.39  ----------------------
% 1.93/1.39  #Subsume      : 0
% 1.93/1.39  #Demod        : 1
% 1.93/1.39  #Tautology    : 5
% 1.93/1.39  #SimpNegUnit  : 0
% 1.93/1.39  #BackRed      : 0
% 1.93/1.39  
% 1.93/1.39  #Partial instantiations: 0
% 1.93/1.39  #Strategies tried      : 1
% 1.93/1.39  
% 1.93/1.39  Timing (in seconds)
% 1.93/1.39  ----------------------
% 1.93/1.40  Preprocessing        : 0.40
% 1.93/1.40  Parsing              : 0.22
% 1.93/1.40  CNF conversion       : 0.02
% 1.93/1.40  Main loop            : 0.12
% 1.93/1.40  Inferencing          : 0.06
% 1.93/1.40  Reduction            : 0.03
% 1.93/1.40  Demodulation         : 0.02
% 1.93/1.40  BG Simplification    : 0.01
% 1.93/1.40  Subsumption          : 0.01
% 1.93/1.40  Abstraction          : 0.01
% 1.93/1.40  MUC search           : 0.00
% 1.93/1.40  Cooper               : 0.00
% 1.93/1.40  Total                : 0.58
% 1.93/1.40  Index Insertion      : 0.00
% 1.93/1.40  Index Deletion       : 0.00
% 1.93/1.40  Index Matching       : 0.00
% 1.93/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

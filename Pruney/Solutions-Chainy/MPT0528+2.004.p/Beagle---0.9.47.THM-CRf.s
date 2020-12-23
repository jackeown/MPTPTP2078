%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:11 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  44 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k8_relat_1(A,k8_relat_1(A,B)) = k8_relat_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k8_relat_1(A_2,B_3))
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = k8_relat_1(A_4,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_23,B_24)),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_4,B_5)),k2_relat_1(k6_relat_1(A_4)))
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_83,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_25,B_26)),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_74])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k8_relat_1(A_6,B_7) = B_7
      | ~ r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [A_29,B_30] :
      ( k8_relat_1(A_29,k8_relat_1(A_29,B_30)) = k8_relat_1(A_29,B_30)
      | ~ v1_relat_1(k8_relat_1(A_29,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_109,plain,(
    ! [A_31,B_32] :
      ( k8_relat_1(A_31,k8_relat_1(A_31,B_32)) = k8_relat_1(A_31,B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_16,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_1','#skF_2')) != k8_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:48:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.22  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.83/1.22  
% 1.83/1.22  %Foreground sorts:
% 1.83/1.22  
% 1.83/1.22  
% 1.83/1.22  %Background operators:
% 1.83/1.22  
% 1.83/1.22  
% 1.83/1.22  %Foreground operators:
% 1.83/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.83/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.22  
% 1.88/1.22  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k8_relat_1(A, k8_relat_1(A, B)) = k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_relat_1)).
% 1.88/1.22  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.88/1.22  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.88/1.22  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.88/1.22  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.88/1.22  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 1.88/1.22  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.88/1.22  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k8_relat_1(A_2, B_3)) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.22  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.22  tff(c_14, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.22  tff(c_6, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=k8_relat_1(A_4, B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.22  tff(c_68, plain, (![A_23, B_24]: (r1_tarski(k2_relat_1(k5_relat_1(A_23, B_24)), k2_relat_1(B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.22  tff(c_74, plain, (![A_4, B_5]: (r1_tarski(k2_relat_1(k8_relat_1(A_4, B_5)), k2_relat_1(k6_relat_1(A_4))) | ~v1_relat_1(k6_relat_1(A_4)) | ~v1_relat_1(B_5) | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 1.88/1.22  tff(c_83, plain, (![A_25, B_26]: (r1_tarski(k2_relat_1(k8_relat_1(A_25, B_26)), A_25) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_74])).
% 1.88/1.22  tff(c_8, plain, (![A_6, B_7]: (k8_relat_1(A_6, B_7)=B_7 | ~r1_tarski(k2_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.22  tff(c_101, plain, (![A_29, B_30]: (k8_relat_1(A_29, k8_relat_1(A_29, B_30))=k8_relat_1(A_29, B_30) | ~v1_relat_1(k8_relat_1(A_29, B_30)) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_83, c_8])).
% 1.88/1.22  tff(c_109, plain, (![A_31, B_32]: (k8_relat_1(A_31, k8_relat_1(A_31, B_32))=k8_relat_1(A_31, B_32) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_4, c_101])).
% 1.88/1.22  tff(c_16, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_1', '#skF_2'))!=k8_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_121, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_16])).
% 1.88/1.22  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_121])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 27
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 0
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 3
% 1.88/1.22  #Demod        : 11
% 1.88/1.22  #Tautology    : 12
% 1.88/1.22  #SimpNegUnit  : 0
% 1.88/1.22  #BackRed      : 0
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.23  Preprocessing        : 0.29
% 1.88/1.23  Parsing              : 0.16
% 1.88/1.23  CNF conversion       : 0.02
% 1.88/1.23  Main loop            : 0.12
% 1.88/1.23  Inferencing          : 0.06
% 1.88/1.23  Reduction            : 0.03
% 1.88/1.23  Demodulation         : 0.02
% 1.88/1.23  BG Simplification    : 0.01
% 1.88/1.23  Subsumption          : 0.02
% 1.88/1.23  Abstraction          : 0.01
% 1.88/1.23  MUC search           : 0.00
% 1.88/1.23  Cooper               : 0.00
% 1.88/1.23  Total                : 0.44
% 1.88/1.23  Index Insertion      : 0.00
% 1.88/1.23  Index Deletion       : 0.00
% 1.88/1.23  Index Matching       : 0.00
% 1.88/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  33 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(k1_relat_1(C),A)
         => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    ! [B_6,A_7] :
      ( k7_relat_1(B_6,A_7) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_7)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_11])).

tff(c_17,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_22,plain,(
    ! [C_8,A_9,B_10] :
      ( k6_subset_1(k7_relat_1(C_8,A_9),k7_relat_1(C_8,B_10)) = k7_relat_1(C_8,k6_subset_1(A_9,B_10))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_10)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_10))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_22])).

tff(c_38,plain,(
    ! [B_10] : k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_10)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_6,plain,(
    k7_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2')) != k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.06  
% 1.57/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.06  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.06  
% 1.61/1.06  %Foreground sorts:
% 1.61/1.06  
% 1.61/1.06  
% 1.61/1.06  %Background operators:
% 1.61/1.06  
% 1.61/1.06  
% 1.61/1.06  %Foreground operators:
% 1.61/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.06  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.61/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.06  
% 1.61/1.07  tff(f_42, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 1.61/1.07  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.61/1.07  tff(f_29, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 1.61/1.07  tff(c_10, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.07  tff(c_8, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.07  tff(c_11, plain, (![B_6, A_7]: (k7_relat_1(B_6, A_7)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_7) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.07  tff(c_14, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_11])).
% 1.61/1.07  tff(c_17, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 1.61/1.07  tff(c_22, plain, (![C_8, A_9, B_10]: (k6_subset_1(k7_relat_1(C_8, A_9), k7_relat_1(C_8, B_10))=k7_relat_1(C_8, k6_subset_1(A_9, B_10)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.07  tff(c_31, plain, (![B_10]: (k7_relat_1('#skF_3', k6_subset_1('#skF_1', B_10))=k6_subset_1('#skF_3', k7_relat_1('#skF_3', B_10)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_17, c_22])).
% 1.61/1.07  tff(c_38, plain, (![B_10]: (k7_relat_1('#skF_3', k6_subset_1('#skF_1', B_10))=k6_subset_1('#skF_3', k7_relat_1('#skF_3', B_10)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 1.61/1.07  tff(c_6, plain, (k7_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2'))!=k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.07  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_6])).
% 1.61/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.07  
% 1.61/1.07  Inference rules
% 1.61/1.07  ----------------------
% 1.61/1.07  #Ref     : 0
% 1.61/1.07  #Sup     : 7
% 1.61/1.07  #Fact    : 0
% 1.61/1.07  #Define  : 0
% 1.61/1.07  #Split   : 0
% 1.61/1.07  #Chain   : 0
% 1.61/1.07  #Close   : 0
% 1.61/1.07  
% 1.61/1.07  Ordering : KBO
% 1.61/1.07  
% 1.61/1.07  Simplification rules
% 1.61/1.07  ----------------------
% 1.61/1.07  #Subsume      : 0
% 1.61/1.07  #Demod        : 4
% 1.61/1.07  #Tautology    : 4
% 1.61/1.07  #SimpNegUnit  : 0
% 1.61/1.07  #BackRed      : 1
% 1.61/1.07  
% 1.61/1.07  #Partial instantiations: 0
% 1.61/1.07  #Strategies tried      : 1
% 1.61/1.07  
% 1.61/1.07  Timing (in seconds)
% 1.61/1.07  ----------------------
% 1.61/1.07  Preprocessing        : 0.24
% 1.61/1.07  Parsing              : 0.13
% 1.61/1.07  CNF conversion       : 0.01
% 1.61/1.07  Main loop            : 0.07
% 1.61/1.07  Inferencing          : 0.03
% 1.61/1.08  Reduction            : 0.02
% 1.61/1.08  Demodulation         : 0.02
% 1.61/1.08  BG Simplification    : 0.01
% 1.61/1.08  Subsumption          : 0.01
% 1.61/1.08  Abstraction          : 0.00
% 1.61/1.08  MUC search           : 0.00
% 1.61/1.08  Cooper               : 0.00
% 1.61/1.08  Total                : 0.33
% 1.61/1.08  Index Insertion      : 0.00
% 1.61/1.08  Index Deletion       : 0.00
% 1.61/1.08  Index Matching       : 0.00
% 1.61/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------

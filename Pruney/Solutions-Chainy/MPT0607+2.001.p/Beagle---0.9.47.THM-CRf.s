%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:28 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  46 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(k1_relat_1(C),A)
         => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_15,plain,(
    ! [B_8,A_9] :
      ( v4_relat_1(B_8,A_9)
      | ~ r1_tarski(k1_relat_1(B_8),A_9)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,
    ( v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_15])).

tff(c_21,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_22,plain,(
    ! [B_10,A_11] :
      ( k7_relat_1(B_10,A_11) = B_10
      | ~ v4_relat_1(B_10,A_11)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_21,c_22])).

tff(c_28,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_25])).

tff(c_38,plain,(
    ! [C_14,A_15,B_16] :
      ( k6_subset_1(k7_relat_1(C_14,A_15),k7_relat_1(C_14,B_16)) = k7_relat_1(C_14,k6_subset_1(A_15,B_16))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [B_16] :
      ( k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_16)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_16))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_54,plain,(
    ! [B_16] : k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_16)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_47])).

tff(c_10,plain,(
    k7_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2')) != k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.43  
% 1.99/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.43  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.43  
% 1.99/1.43  %Foreground sorts:
% 1.99/1.43  
% 1.99/1.43  
% 1.99/1.43  %Background operators:
% 1.99/1.43  
% 1.99/1.43  
% 1.99/1.43  %Foreground operators:
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.99/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.43  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.43  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.99/1.43  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.43  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.99/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.43  
% 1.99/1.44  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 1.99/1.44  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.99/1.44  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.99/1.44  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 1.99/1.44  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.44  tff(c_12, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.44  tff(c_15, plain, (![B_8, A_9]: (v4_relat_1(B_8, A_9) | ~r1_tarski(k1_relat_1(B_8), A_9) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.44  tff(c_18, plain, (v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_15])).
% 1.99/1.44  tff(c_21, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 1.99/1.44  tff(c_22, plain, (![B_10, A_11]: (k7_relat_1(B_10, A_11)=B_10 | ~v4_relat_1(B_10, A_11) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.44  tff(c_25, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_21, c_22])).
% 1.99/1.44  tff(c_28, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_25])).
% 1.99/1.44  tff(c_38, plain, (![C_14, A_15, B_16]: (k6_subset_1(k7_relat_1(C_14, A_15), k7_relat_1(C_14, B_16))=k7_relat_1(C_14, k6_subset_1(A_15, B_16)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.44  tff(c_47, plain, (![B_16]: (k7_relat_1('#skF_3', k6_subset_1('#skF_1', B_16))=k6_subset_1('#skF_3', k7_relat_1('#skF_3', B_16)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_38])).
% 1.99/1.44  tff(c_54, plain, (![B_16]: (k7_relat_1('#skF_3', k6_subset_1('#skF_1', B_16))=k6_subset_1('#skF_3', k7_relat_1('#skF_3', B_16)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_47])).
% 1.99/1.44  tff(c_10, plain, (k7_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2'))!=k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.44  tff(c_59, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 1.99/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.44  
% 1.99/1.44  Inference rules
% 1.99/1.44  ----------------------
% 1.99/1.44  #Ref     : 0
% 1.99/1.44  #Sup     : 9
% 1.99/1.44  #Fact    : 0
% 1.99/1.44  #Define  : 0
% 1.99/1.44  #Split   : 0
% 1.99/1.44  #Chain   : 0
% 1.99/1.44  #Close   : 0
% 1.99/1.44  
% 1.99/1.44  Ordering : KBO
% 1.99/1.44  
% 1.99/1.44  Simplification rules
% 1.99/1.44  ----------------------
% 1.99/1.44  #Subsume      : 0
% 1.99/1.44  #Demod        : 5
% 1.99/1.44  #Tautology    : 5
% 1.99/1.44  #SimpNegUnit  : 0
% 1.99/1.44  #BackRed      : 1
% 1.99/1.44  
% 1.99/1.44  #Partial instantiations: 0
% 1.99/1.44  #Strategies tried      : 1
% 1.99/1.44  
% 1.99/1.44  Timing (in seconds)
% 1.99/1.44  ----------------------
% 1.99/1.45  Preprocessing        : 0.44
% 1.99/1.45  Parsing              : 0.23
% 1.99/1.45  CNF conversion       : 0.03
% 1.99/1.45  Main loop            : 0.14
% 1.99/1.45  Inferencing          : 0.06
% 1.99/1.45  Reduction            : 0.04
% 1.99/1.45  Demodulation         : 0.03
% 1.99/1.45  BG Simplification    : 0.01
% 1.99/1.45  Subsumption          : 0.02
% 1.99/1.45  Abstraction          : 0.01
% 1.99/1.45  MUC search           : 0.00
% 1.99/1.45  Cooper               : 0.00
% 1.99/1.45  Total                : 0.62
% 1.99/1.45  Index Insertion      : 0.00
% 1.99/1.45  Index Deletion       : 0.00
% 1.99/1.45  Index Matching       : 0.00
% 1.99/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   30 (  38 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  52 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k2_zfmisc_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(k1_relat_1(C),A)
         => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_9] :
      ( k7_relat_1(A_9,k1_relat_1(A_9)) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_29,plain,(
    ! [C_13,A_14,B_15] :
      ( k7_relat_1(k7_relat_1(C_13,A_14),B_15) = k7_relat_1(C_13,A_14)
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_19,B_20] :
      ( k7_relat_1(A_19,k1_relat_1(A_19)) = k7_relat_1(A_19,B_20)
      | ~ r1_tarski(k1_relat_1(A_19),B_20)
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_29])).

tff(c_80,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_78])).

tff(c_83,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_96,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_8])).

tff(c_109,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_96])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( k6_subset_1(k7_relat_1(C_8,A_6),k7_relat_1(C_8,B_7)) = k7_relat_1(C_8,k6_subset_1(A_6,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [B_7] :
      ( k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_7)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_7))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_6])).

tff(c_127,plain,(
    ! [B_7] : k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_7)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_10,plain,(
    k7_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2')) != k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:50:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.19  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k2_zfmisc_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.80/1.19  
% 1.80/1.19  %Foreground sorts:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Background operators:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Foreground operators:
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.80/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.19  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.80/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.19  
% 1.80/1.19  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 1.80/1.19  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.80/1.19  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.80/1.19  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 1.80/1.19  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.19  tff(c_12, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.19  tff(c_8, plain, (![A_9]: (k7_relat_1(A_9, k1_relat_1(A_9))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.19  tff(c_29, plain, (![C_13, A_14, B_15]: (k7_relat_1(k7_relat_1(C_13, A_14), B_15)=k7_relat_1(C_13, A_14) | ~r1_tarski(A_14, B_15) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.19  tff(c_78, plain, (![A_19, B_20]: (k7_relat_1(A_19, k1_relat_1(A_19))=k7_relat_1(A_19, B_20) | ~r1_tarski(k1_relat_1(A_19), B_20) | ~v1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_8, c_29])).
% 1.80/1.19  tff(c_80, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_78])).
% 1.80/1.19  tff(c_83, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 1.80/1.19  tff(c_96, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_83, c_8])).
% 1.80/1.19  tff(c_109, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_96])).
% 1.80/1.19  tff(c_6, plain, (![C_8, A_6, B_7]: (k6_subset_1(k7_relat_1(C_8, A_6), k7_relat_1(C_8, B_7))=k7_relat_1(C_8, k6_subset_1(A_6, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.19  tff(c_117, plain, (![B_7]: (k7_relat_1('#skF_3', k6_subset_1('#skF_1', B_7))=k6_subset_1('#skF_3', k7_relat_1('#skF_3', B_7)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_6])).
% 1.80/1.19  tff(c_127, plain, (![B_7]: (k7_relat_1('#skF_3', k6_subset_1('#skF_1', B_7))=k6_subset_1('#skF_3', k7_relat_1('#skF_3', B_7)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_117])).
% 1.80/1.19  tff(c_10, plain, (k7_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2'))!=k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.19  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_10])).
% 1.80/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  Inference rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Ref     : 1
% 1.80/1.19  #Sup     : 36
% 1.80/1.19  #Fact    : 0
% 1.80/1.19  #Define  : 0
% 1.80/1.19  #Split   : 0
% 1.80/1.19  #Chain   : 0
% 1.80/1.20  #Close   : 0
% 1.80/1.20  
% 1.80/1.20  Ordering : KBO
% 1.80/1.20  
% 1.80/1.20  Simplification rules
% 1.80/1.20  ----------------------
% 1.80/1.20  #Subsume      : 0
% 1.80/1.20  #Demod        : 21
% 1.80/1.20  #Tautology    : 19
% 1.80/1.20  #SimpNegUnit  : 0
% 1.80/1.20  #BackRed      : 2
% 1.80/1.20  
% 1.80/1.20  #Partial instantiations: 0
% 1.80/1.20  #Strategies tried      : 1
% 1.80/1.20  
% 1.80/1.20  Timing (in seconds)
% 1.80/1.20  ----------------------
% 1.80/1.20  Preprocessing        : 0.27
% 1.80/1.20  Parsing              : 0.15
% 1.80/1.20  CNF conversion       : 0.02
% 1.80/1.20  Main loop            : 0.13
% 1.80/1.20  Inferencing          : 0.06
% 1.80/1.20  Reduction            : 0.04
% 1.80/1.20  Demodulation         : 0.03
% 1.80/1.20  BG Simplification    : 0.01
% 1.80/1.20  Subsumption          : 0.02
% 1.80/1.20  Abstraction          : 0.01
% 1.80/1.20  MUC search           : 0.00
% 1.80/1.20  Cooper               : 0.00
% 1.80/1.20  Total                : 0.43
% 1.80/1.20  Index Insertion      : 0.00
% 1.80/1.20  Index Deletion       : 0.00
% 1.80/1.20  Index Matching       : 0.00
% 1.80/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

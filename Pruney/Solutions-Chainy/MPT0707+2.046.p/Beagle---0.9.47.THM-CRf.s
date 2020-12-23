%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:22 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [B_19,A_20] :
      ( k5_relat_1(B_19,k6_relat_1(A_20)) = B_19
      | ~ r1_tarski(k2_relat_1(B_19),A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [A_6,A_20] :
      ( k5_relat_1(k6_relat_1(A_6),k6_relat_1(A_20)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_20)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_59,plain,(
    ! [A_6,A_20] :
      ( k5_relat_1(k6_relat_1(A_6),k6_relat_1(A_20)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_57])).

tff(c_69,plain,(
    ! [B_23,A_24] :
      ( k9_relat_1(B_23,k2_relat_1(A_24)) = k2_relat_1(k5_relat_1(A_24,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,(
    ! [A_6,B_23] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_6),B_23)) = k9_relat_1(B_23,A_6)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_83,plain,(
    ! [A_25,B_26] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_25),B_26)) = k9_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_78])).

tff(c_98,plain,(
    ! [A_20,A_6] :
      ( k9_relat_1(k6_relat_1(A_20),A_6) = k2_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ r1_tarski(A_6,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_83])).

tff(c_103,plain,(
    ! [A_27,A_28] :
      ( k9_relat_1(k6_relat_1(A_27),A_28) = A_28
      | ~ r1_tarski(A_28,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_98])).

tff(c_20,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_20])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.79/1.19  
% 1.79/1.19  %Foreground sorts:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Background operators:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Foreground operators:
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.79/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.79/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.79/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.79/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.19  
% 1.79/1.20  tff(f_57, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.79/1.20  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.79/1.20  tff(f_52, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 1.79/1.20  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.79/1.20  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.79/1.20  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.79/1.20  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.79/1.20  tff(c_45, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.20  tff(c_53, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_45])).
% 1.79/1.20  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.79/1.20  tff(c_10, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.20  tff(c_54, plain, (![B_19, A_20]: (k5_relat_1(B_19, k6_relat_1(A_20))=B_19 | ~r1_tarski(k2_relat_1(B_19), A_20) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.20  tff(c_57, plain, (![A_6, A_20]: (k5_relat_1(k6_relat_1(A_6), k6_relat_1(A_20))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_20) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_54])).
% 1.79/1.20  tff(c_59, plain, (![A_6, A_20]: (k5_relat_1(k6_relat_1(A_6), k6_relat_1(A_20))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_57])).
% 1.79/1.20  tff(c_69, plain, (![B_23, A_24]: (k9_relat_1(B_23, k2_relat_1(A_24))=k2_relat_1(k5_relat_1(A_24, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.20  tff(c_78, plain, (![A_6, B_23]: (k2_relat_1(k5_relat_1(k6_relat_1(A_6), B_23))=k9_relat_1(B_23, A_6) | ~v1_relat_1(B_23) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_69])).
% 1.79/1.20  tff(c_83, plain, (![A_25, B_26]: (k2_relat_1(k5_relat_1(k6_relat_1(A_25), B_26))=k9_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_78])).
% 1.79/1.20  tff(c_98, plain, (![A_20, A_6]: (k9_relat_1(k6_relat_1(A_20), A_6)=k2_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_20)) | ~r1_tarski(A_6, A_20))), inference(superposition, [status(thm), theory('equality')], [c_59, c_83])).
% 1.79/1.20  tff(c_103, plain, (![A_27, A_28]: (k9_relat_1(k6_relat_1(A_27), A_28)=A_28 | ~r1_tarski(A_28, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_98])).
% 1.79/1.20  tff(c_20, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.79/1.20  tff(c_113, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103, c_20])).
% 1.79/1.20  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_113])).
% 1.79/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  Inference rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Ref     : 0
% 1.79/1.20  #Sup     : 22
% 1.79/1.20  #Fact    : 0
% 1.79/1.20  #Define  : 0
% 1.79/1.20  #Split   : 0
% 1.79/1.20  #Chain   : 0
% 1.79/1.20  #Close   : 0
% 1.79/1.20  
% 1.79/1.20  Ordering : KBO
% 1.79/1.20  
% 1.79/1.20  Simplification rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Subsume      : 0
% 1.79/1.20  #Demod        : 6
% 1.79/1.20  #Tautology    : 12
% 1.79/1.20  #SimpNegUnit  : 0
% 1.79/1.20  #BackRed      : 0
% 1.79/1.20  
% 1.79/1.20  #Partial instantiations: 0
% 1.79/1.20  #Strategies tried      : 1
% 1.79/1.20  
% 1.79/1.20  Timing (in seconds)
% 1.79/1.20  ----------------------
% 1.79/1.20  Preprocessing        : 0.29
% 1.79/1.20  Parsing              : 0.16
% 1.79/1.20  CNF conversion       : 0.02
% 1.79/1.20  Main loop            : 0.11
% 1.79/1.20  Inferencing          : 0.05
% 1.79/1.20  Reduction            : 0.03
% 1.79/1.20  Demodulation         : 0.03
% 1.79/1.20  BG Simplification    : 0.01
% 1.79/1.20  Subsumption          : 0.01
% 1.79/1.20  Abstraction          : 0.01
% 1.79/1.20  MUC search           : 0.00
% 1.79/1.20  Cooper               : 0.00
% 1.79/1.20  Total                : 0.43
% 1.79/1.20  Index Insertion      : 0.00
% 1.79/1.20  Index Deletion       : 0.00
% 1.79/1.20  Index Matching       : 0.00
% 1.79/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

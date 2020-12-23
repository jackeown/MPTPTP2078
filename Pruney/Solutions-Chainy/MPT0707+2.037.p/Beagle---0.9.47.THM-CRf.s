%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:21 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  59 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    ! [B_24,A_25] :
      ( k5_relat_1(B_24,k6_relat_1(A_25)) = k8_relat_1(A_25,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    ! [A_25,A_11] :
      ( k8_relat_1(A_25,k6_relat_1(A_11)) = k7_relat_1(k6_relat_1(A_25),A_11)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_87,plain,(
    ! [A_25,A_11] : k8_relat_1(A_25,k6_relat_1(A_11)) = k7_relat_1(k6_relat_1(A_25),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_77])).

tff(c_101,plain,(
    ! [A_28,B_29] :
      ( k8_relat_1(A_28,B_29) = B_29
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_28,A_10] :
      ( k8_relat_1(A_28,k6_relat_1(A_10)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_28)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_101])).

tff(c_110,plain,(
    ! [A_30,A_31] :
      ( k7_relat_1(k6_relat_1(A_30),A_31) = k6_relat_1(A_31)
      | ~ r1_tarski(A_31,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_87,c_107])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [A_30,A_31] :
      ( k9_relat_1(k6_relat_1(A_30),A_31) = k2_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ r1_tarski(A_31,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_125,plain,(
    ! [A_35,A_36] :
      ( k9_relat_1(k6_relat_1(A_35),A_36) = A_36
      | ~ r1_tarski(A_36,A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16,c_116])).

tff(c_20,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_134,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_20])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.45  
% 2.17/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.45  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.17/1.45  
% 2.17/1.45  %Foreground sorts:
% 2.17/1.45  
% 2.17/1.45  
% 2.17/1.45  %Background operators:
% 2.17/1.45  
% 2.17/1.45  
% 2.17/1.45  %Foreground operators:
% 2.17/1.45  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.17/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.17/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.45  
% 2.17/1.47  tff(f_58, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.17/1.47  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.47  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.17/1.47  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.17/1.47  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.17/1.47  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.17/1.47  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.17/1.47  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.17/1.47  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.47  tff(c_42, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.47  tff(c_46, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_42])).
% 2.17/1.47  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.47  tff(c_16, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.47  tff(c_70, plain, (![B_24, A_25]: (k5_relat_1(B_24, k6_relat_1(A_25))=k8_relat_1(A_25, B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.47  tff(c_18, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.47  tff(c_77, plain, (![A_25, A_11]: (k8_relat_1(A_25, k6_relat_1(A_11))=k7_relat_1(k6_relat_1(A_25), A_11) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_18])).
% 2.17/1.47  tff(c_87, plain, (![A_25, A_11]: (k8_relat_1(A_25, k6_relat_1(A_11))=k7_relat_1(k6_relat_1(A_25), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_77])).
% 2.17/1.47  tff(c_101, plain, (![A_28, B_29]: (k8_relat_1(A_28, B_29)=B_29 | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.47  tff(c_107, plain, (![A_28, A_10]: (k8_relat_1(A_28, k6_relat_1(A_10))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_28) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_101])).
% 2.17/1.47  tff(c_110, plain, (![A_30, A_31]: (k7_relat_1(k6_relat_1(A_30), A_31)=k6_relat_1(A_31) | ~r1_tarski(A_31, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_87, c_107])).
% 2.17/1.47  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.47  tff(c_116, plain, (![A_30, A_31]: (k9_relat_1(k6_relat_1(A_30), A_31)=k2_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(k6_relat_1(A_30)) | ~r1_tarski(A_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 2.17/1.47  tff(c_125, plain, (![A_35, A_36]: (k9_relat_1(k6_relat_1(A_35), A_36)=A_36 | ~r1_tarski(A_36, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16, c_116])).
% 2.17/1.47  tff(c_20, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.47  tff(c_134, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_125, c_20])).
% 2.17/1.47  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_134])).
% 2.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.47  
% 2.17/1.47  Inference rules
% 2.17/1.47  ----------------------
% 2.17/1.47  #Ref     : 0
% 2.17/1.47  #Sup     : 25
% 2.17/1.47  #Fact    : 0
% 2.17/1.47  #Define  : 0
% 2.17/1.47  #Split   : 0
% 2.17/1.47  #Chain   : 0
% 2.17/1.47  #Close   : 0
% 2.17/1.47  
% 2.17/1.47  Ordering : KBO
% 2.17/1.47  
% 2.17/1.47  Simplification rules
% 2.17/1.47  ----------------------
% 2.17/1.47  #Subsume      : 0
% 2.17/1.47  #Demod        : 11
% 2.17/1.47  #Tautology    : 17
% 2.17/1.47  #SimpNegUnit  : 0
% 2.17/1.47  #BackRed      : 0
% 2.17/1.47  
% 2.17/1.47  #Partial instantiations: 0
% 2.17/1.47  #Strategies tried      : 1
% 2.17/1.47  
% 2.17/1.47  Timing (in seconds)
% 2.17/1.47  ----------------------
% 2.17/1.47  Preprocessing        : 0.44
% 2.17/1.47  Parsing              : 0.25
% 2.17/1.47  CNF conversion       : 0.03
% 2.17/1.47  Main loop            : 0.21
% 2.17/1.47  Inferencing          : 0.10
% 2.17/1.47  Reduction            : 0.06
% 2.17/1.47  Demodulation         : 0.04
% 2.17/1.47  BG Simplification    : 0.02
% 2.17/1.47  Subsumption          : 0.02
% 2.17/1.47  Abstraction          : 0.01
% 2.17/1.47  MUC search           : 0.00
% 2.17/1.47  Cooper               : 0.00
% 2.17/1.47  Total                : 0.70
% 2.17/1.47  Index Insertion      : 0.00
% 2.17/1.47  Index Deletion       : 0.00
% 2.17/1.47  Index Matching       : 0.00
% 2.17/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

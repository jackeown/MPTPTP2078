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

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  54 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_54,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [B_22,A_23] :
      ( k5_relat_1(B_22,k6_relat_1(A_23)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_6,A_23] :
      ( k5_relat_1(k6_relat_1(A_6),k6_relat_1(A_23)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_23)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_68])).

tff(c_77,plain,(
    ! [A_24,A_25] :
      ( k5_relat_1(k6_relat_1(A_24),k6_relat_1(A_25)) = k6_relat_1(A_24)
      | ~ r1_tarski(A_24,A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_25,A_24] :
      ( k7_relat_1(k6_relat_1(A_25),A_24) = k6_relat_1(A_24)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ r1_tarski(A_24,A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_16])).

tff(c_97,plain,(
    ! [A_26,A_27] :
      ( k7_relat_1(k6_relat_1(A_26),A_27) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_83])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [A_26,A_27] :
      ( k9_relat_1(k6_relat_1(A_26),A_27) = k2_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ r1_tarski(A_27,A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_8])).

tff(c_111,plain,(
    ! [A_28,A_29] :
      ( k9_relat_1(k6_relat_1(A_28),A_29) = A_29
      | ~ r1_tarski(A_29,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_103])).

tff(c_18,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_117,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_18])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:50:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.20  
% 1.77/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.20  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.77/1.20  
% 1.77/1.20  %Foreground sorts:
% 1.77/1.20  
% 1.77/1.20  
% 1.77/1.20  %Background operators:
% 1.77/1.20  
% 1.77/1.20  
% 1.77/1.20  %Foreground operators:
% 1.77/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.77/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.77/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.77/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.77/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.20  
% 1.77/1.21  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.77/1.21  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.77/1.21  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.77/1.21  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.77/1.21  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.77/1.21  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.77/1.21  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.77/1.21  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.21  tff(c_40, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.21  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_40])).
% 1.77/1.21  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.21  tff(c_12, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.21  tff(c_68, plain, (![B_22, A_23]: (k5_relat_1(B_22, k6_relat_1(A_23))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.77/1.21  tff(c_74, plain, (![A_6, A_23]: (k5_relat_1(k6_relat_1(A_6), k6_relat_1(A_23))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_23) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_68])).
% 1.77/1.21  tff(c_77, plain, (![A_24, A_25]: (k5_relat_1(k6_relat_1(A_24), k6_relat_1(A_25))=k6_relat_1(A_24) | ~r1_tarski(A_24, A_25))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_74])).
% 1.77/1.21  tff(c_16, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.77/1.21  tff(c_83, plain, (![A_25, A_24]: (k7_relat_1(k6_relat_1(A_25), A_24)=k6_relat_1(A_24) | ~v1_relat_1(k6_relat_1(A_25)) | ~r1_tarski(A_24, A_25))), inference(superposition, [status(thm), theory('equality')], [c_77, c_16])).
% 1.77/1.21  tff(c_97, plain, (![A_26, A_27]: (k7_relat_1(k6_relat_1(A_26), A_27)=k6_relat_1(A_27) | ~r1_tarski(A_27, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_83])).
% 1.77/1.21  tff(c_8, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.21  tff(c_103, plain, (![A_26, A_27]: (k9_relat_1(k6_relat_1(A_26), A_27)=k2_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_26)) | ~r1_tarski(A_27, A_26))), inference(superposition, [status(thm), theory('equality')], [c_97, c_8])).
% 1.77/1.21  tff(c_111, plain, (![A_28, A_29]: (k9_relat_1(k6_relat_1(A_28), A_29)=A_29 | ~r1_tarski(A_29, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_103])).
% 1.77/1.21  tff(c_18, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.21  tff(c_117, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111, c_18])).
% 1.77/1.21  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_117])).
% 1.77/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.21  
% 1.77/1.21  Inference rules
% 1.77/1.21  ----------------------
% 1.77/1.21  #Ref     : 0
% 1.77/1.21  #Sup     : 22
% 1.77/1.21  #Fact    : 0
% 1.77/1.21  #Define  : 0
% 1.77/1.21  #Split   : 0
% 1.77/1.21  #Chain   : 0
% 1.77/1.21  #Close   : 0
% 1.77/1.21  
% 1.77/1.21  Ordering : KBO
% 1.77/1.21  
% 1.77/1.21  Simplification rules
% 1.77/1.21  ----------------------
% 1.77/1.21  #Subsume      : 0
% 1.77/1.21  #Demod        : 6
% 1.77/1.21  #Tautology    : 14
% 1.77/1.21  #SimpNegUnit  : 0
% 1.77/1.21  #BackRed      : 0
% 1.77/1.21  
% 1.77/1.21  #Partial instantiations: 0
% 1.77/1.21  #Strategies tried      : 1
% 1.77/1.21  
% 1.77/1.21  Timing (in seconds)
% 1.77/1.21  ----------------------
% 1.77/1.22  Preprocessing        : 0.28
% 1.77/1.22  Parsing              : 0.16
% 1.77/1.22  CNF conversion       : 0.02
% 1.77/1.22  Main loop            : 0.12
% 1.77/1.22  Inferencing          : 0.06
% 1.77/1.22  Reduction            : 0.03
% 1.77/1.22  Demodulation         : 0.02
% 1.77/1.22  BG Simplification    : 0.01
% 1.77/1.22  Subsumption          : 0.01
% 1.77/1.22  Abstraction          : 0.01
% 1.77/1.22  MUC search           : 0.00
% 1.77/1.22  Cooper               : 0.00
% 1.77/1.22  Total                : 0.43
% 1.77/1.22  Index Insertion      : 0.00
% 1.77/1.22  Index Deletion       : 0.00
% 1.77/1.22  Index Matching       : 0.00
% 1.77/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

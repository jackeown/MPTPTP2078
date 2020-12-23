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
% DateTime   : Thu Dec  3 10:05:23 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  58 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [B_18,A_19] :
      ( k5_relat_1(B_18,k6_relat_1(A_19)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    ! [A_6,A_19] :
      ( k5_relat_1(k6_relat_1(A_6),k6_relat_1(A_19)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_19)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_56,plain,(
    ! [A_6,A_19] :
      ( k5_relat_1(k6_relat_1(A_6),k6_relat_1(A_19)) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_66,plain,(
    ! [B_22,A_23] :
      ( k9_relat_1(B_22,k2_relat_1(A_23)) = k2_relat_1(k5_relat_1(A_23,B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,(
    ! [A_6,B_22] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_6),B_22)) = k9_relat_1(B_22,A_6)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_80,plain,(
    ! [A_24,B_25] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_24),B_25)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_75])).

tff(c_95,plain,(
    ! [A_19,A_6] :
      ( k9_relat_1(k6_relat_1(A_19),A_6) = k2_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ r1_tarski(A_6,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_80])).

tff(c_100,plain,(
    ! [A_26,A_27] :
      ( k9_relat_1(k6_relat_1(A_26),A_27) = A_27
      | ~ r1_tarski(A_27,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_95])).

tff(c_18,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_110,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_110])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.81/1.18  
% 1.81/1.18  %Foreground sorts:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Background operators:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Foreground operators:
% 1.81/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.81/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.81/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.18  
% 1.81/1.19  tff(f_55, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.81/1.19  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.81/1.19  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.81/1.19  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.81/1.19  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.81/1.19  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 1.81/1.19  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.19  tff(c_42, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.19  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_42])).
% 1.81/1.19  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.19  tff(c_10, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.19  tff(c_51, plain, (![B_18, A_19]: (k5_relat_1(B_18, k6_relat_1(A_19))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.19  tff(c_54, plain, (![A_6, A_19]: (k5_relat_1(k6_relat_1(A_6), k6_relat_1(A_19))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_19) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_51])).
% 1.81/1.19  tff(c_56, plain, (![A_6, A_19]: (k5_relat_1(k6_relat_1(A_6), k6_relat_1(A_19))=k6_relat_1(A_6) | ~r1_tarski(A_6, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 1.81/1.19  tff(c_66, plain, (![B_22, A_23]: (k9_relat_1(B_22, k2_relat_1(A_23))=k2_relat_1(k5_relat_1(A_23, B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.19  tff(c_75, plain, (![A_6, B_22]: (k2_relat_1(k5_relat_1(k6_relat_1(A_6), B_22))=k9_relat_1(B_22, A_6) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_66])).
% 1.81/1.19  tff(c_80, plain, (![A_24, B_25]: (k2_relat_1(k5_relat_1(k6_relat_1(A_24), B_25))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_75])).
% 1.81/1.19  tff(c_95, plain, (![A_19, A_6]: (k9_relat_1(k6_relat_1(A_19), A_6)=k2_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_19)) | ~r1_tarski(A_6, A_19))), inference(superposition, [status(thm), theory('equality')], [c_56, c_80])).
% 1.81/1.19  tff(c_100, plain, (![A_26, A_27]: (k9_relat_1(k6_relat_1(A_26), A_27)=A_27 | ~r1_tarski(A_27, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_95])).
% 1.81/1.19  tff(c_18, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.19  tff(c_110, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_18])).
% 1.81/1.19  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_110])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 22
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 6
% 1.81/1.19  #Tautology    : 12
% 1.81/1.19  #SimpNegUnit  : 0
% 1.81/1.19  #BackRed      : 0
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.20  Preprocessing        : 0.27
% 1.81/1.20  Parsing              : 0.14
% 1.81/1.20  CNF conversion       : 0.02
% 1.81/1.20  Main loop            : 0.14
% 1.81/1.20  Inferencing          : 0.07
% 1.81/1.20  Reduction            : 0.04
% 1.81/1.20  Demodulation         : 0.03
% 1.81/1.20  BG Simplification    : 0.01
% 1.81/1.20  Subsumption          : 0.01
% 1.81/1.20  Abstraction          : 0.01
% 1.81/1.20  MUC search           : 0.00
% 1.81/1.20  Cooper               : 0.00
% 1.81/1.20  Total                : 0.44
% 1.81/1.20  Index Insertion      : 0.00
% 1.81/1.20  Index Deletion       : 0.00
% 1.81/1.20  Index Matching       : 0.00
% 1.81/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

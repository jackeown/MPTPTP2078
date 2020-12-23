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
% DateTime   : Thu Dec  3 09:59:38 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   34 (  52 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  93 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => r1_tarski(k5_relat_1(B,k7_relat_1(C,A)),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_29,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(A_24)
      | ~ v1_relat_1(B_25)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_4,c_24])).

tff(c_33,plain,(
    ! [B_14,A_13] :
      ( v1_relat_1(k7_relat_1(B_14,A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_10,c_29])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    ! [C_28,A_29,B_30] :
      ( r1_tarski(k5_relat_1(C_28,A_29),k5_relat_1(C_28,B_30))
      | ~ r1_tarski(A_29,B_30)
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ~ r1_tarski(k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_35,c_12])).

tff(c_44,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_38])).

tff(c_46,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_49,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_46])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_49])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_58,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_54])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.07  
% 1.66/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.07  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.07  
% 1.66/1.07  %Foreground sorts:
% 1.66/1.07  
% 1.66/1.07  
% 1.66/1.07  %Background operators:
% 1.66/1.07  
% 1.66/1.07  
% 1.66/1.07  %Foreground operators:
% 1.66/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.66/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.07  
% 1.66/1.08  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(B, k7_relat_1(C, A)), k5_relat_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_relat_1)).
% 1.66/1.08  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.66/1.08  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.66/1.08  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.66/1.08  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 1.66/1.08  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.66/1.08  tff(c_10, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.08  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.08  tff(c_24, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.66/1.08  tff(c_29, plain, (![A_24, B_25]: (v1_relat_1(A_24) | ~v1_relat_1(B_25) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_4, c_24])).
% 1.66/1.08  tff(c_33, plain, (![B_14, A_13]: (v1_relat_1(k7_relat_1(B_14, A_13)) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_10, c_29])).
% 1.66/1.08  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.66/1.08  tff(c_35, plain, (![C_28, A_29, B_30]: (r1_tarski(k5_relat_1(C_28, A_29), k5_relat_1(C_28, B_30)) | ~r1_tarski(A_29, B_30) | ~v1_relat_1(C_28) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.66/1.08  tff(c_12, plain, (~r1_tarski(k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1')), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.66/1.08  tff(c_38, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_35, c_12])).
% 1.66/1.08  tff(c_44, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_38])).
% 1.66/1.08  tff(c_46, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 1.66/1.08  tff(c_49, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_33, c_46])).
% 1.66/1.08  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_49])).
% 1.66/1.08  tff(c_54, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 1.66/1.08  tff(c_58, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_54])).
% 1.66/1.08  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 1.66/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.08  
% 1.66/1.08  Inference rules
% 1.66/1.08  ----------------------
% 1.66/1.08  #Ref     : 0
% 1.66/1.08  #Sup     : 7
% 1.66/1.08  #Fact    : 0
% 1.66/1.08  #Define  : 0
% 1.66/1.08  #Split   : 1
% 1.66/1.08  #Chain   : 0
% 1.66/1.08  #Close   : 0
% 1.66/1.08  
% 1.66/1.08  Ordering : KBO
% 1.66/1.08  
% 1.66/1.08  Simplification rules
% 1.66/1.08  ----------------------
% 1.66/1.08  #Subsume      : 0
% 1.66/1.08  #Demod        : 4
% 1.66/1.08  #Tautology    : 1
% 1.66/1.08  #SimpNegUnit  : 0
% 1.66/1.08  #BackRed      : 0
% 1.66/1.08  
% 1.66/1.08  #Partial instantiations: 0
% 1.66/1.08  #Strategies tried      : 1
% 1.66/1.08  
% 1.66/1.08  Timing (in seconds)
% 1.66/1.08  ----------------------
% 1.66/1.09  Preprocessing        : 0.24
% 1.66/1.09  Parsing              : 0.14
% 1.66/1.09  CNF conversion       : 0.02
% 1.66/1.09  Main loop            : 0.10
% 1.66/1.09  Inferencing          : 0.05
% 1.66/1.09  Reduction            : 0.02
% 1.66/1.09  Demodulation         : 0.02
% 1.66/1.09  BG Simplification    : 0.01
% 1.66/1.09  Subsumption          : 0.02
% 1.66/1.09  Abstraction          : 0.00
% 1.66/1.09  MUC search           : 0.00
% 1.66/1.09  Cooper               : 0.00
% 1.66/1.09  Total                : 0.37
% 1.66/1.09  Index Insertion      : 0.00
% 1.66/1.09  Index Deletion       : 0.00
% 1.66/1.09  Index Matching       : 0.00
% 1.66/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

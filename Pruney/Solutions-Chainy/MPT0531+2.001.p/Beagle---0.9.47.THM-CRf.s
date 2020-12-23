%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:15 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  62 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k8_relat_1(A_11,B_12),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [C_22,A_23] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [C_22,A_23] :
      ( m1_subset_1(C_22,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(resolution,[status(thm)],[c_30,c_14])).

tff(c_40,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ! [C_30,A_31] :
      ( v1_relat_1(C_30)
      | ~ v1_relat_1(A_31)
      | ~ r1_tarski(C_30,A_31) ) ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_53,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k8_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    ! [A_40,B_41,C_42] :
      ( k8_relat_1(A_40,k8_relat_1(B_41,C_42)) = k8_relat_1(A_40,C_42)
      | ~ r1_tarski(A_40,B_41)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_154,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(k8_relat_1(A_53,C_54),k8_relat_1(B_55,C_54))
      | ~ v1_relat_1(k8_relat_1(B_55,C_54))
      | ~ r1_tarski(A_53,B_55)
      | ~ v1_relat_1(C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_18])).

tff(c_22,plain,(
    ~ r1_tarski(k8_relat_1('#skF_3','#skF_5'),k8_relat_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_154,c_22])).

tff(c_170,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_160])).

tff(c_179,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_53,c_170])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.33  
% 2.05/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.34  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.05/1.34  
% 2.05/1.34  %Foreground sorts:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Background operators:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Foreground operators:
% 2.05/1.34  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.34  
% 2.05/1.35  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 2.05/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.05/1.35  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.05/1.35  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.05/1.35  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.05/1.35  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 2.05/1.35  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.35  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k8_relat_1(A_11, B_12), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.35  tff(c_30, plain, (![C_22, A_23]: (r2_hidden(C_22, k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.35  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.05/1.35  tff(c_38, plain, (![C_22, A_23]: (m1_subset_1(C_22, k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(resolution, [status(thm)], [c_30, c_14])).
% 2.05/1.35  tff(c_40, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.35  tff(c_46, plain, (![C_30, A_31]: (v1_relat_1(C_30) | ~v1_relat_1(A_31) | ~r1_tarski(C_30, A_31))), inference(resolution, [status(thm)], [c_38, c_40])).
% 2.05/1.35  tff(c_53, plain, (![A_11, B_12]: (v1_relat_1(k8_relat_1(A_11, B_12)) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_18, c_46])).
% 2.05/1.35  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.35  tff(c_86, plain, (![A_40, B_41, C_42]: (k8_relat_1(A_40, k8_relat_1(B_41, C_42))=k8_relat_1(A_40, C_42) | ~r1_tarski(A_40, B_41) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.35  tff(c_154, plain, (![A_53, C_54, B_55]: (r1_tarski(k8_relat_1(A_53, C_54), k8_relat_1(B_55, C_54)) | ~v1_relat_1(k8_relat_1(B_55, C_54)) | ~r1_tarski(A_53, B_55) | ~v1_relat_1(C_54))), inference(superposition, [status(thm), theory('equality')], [c_86, c_18])).
% 2.05/1.35  tff(c_22, plain, (~r1_tarski(k8_relat_1('#skF_3', '#skF_5'), k8_relat_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.35  tff(c_160, plain, (~v1_relat_1(k8_relat_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_154, c_22])).
% 2.05/1.35  tff(c_170, plain, (~v1_relat_1(k8_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_160])).
% 2.05/1.35  tff(c_179, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_53, c_170])).
% 2.05/1.35  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_179])).
% 2.05/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.35  
% 2.05/1.35  Inference rules
% 2.05/1.35  ----------------------
% 2.05/1.35  #Ref     : 0
% 2.05/1.35  #Sup     : 32
% 2.05/1.35  #Fact    : 0
% 2.05/1.35  #Define  : 0
% 2.05/1.35  #Split   : 1
% 2.05/1.35  #Chain   : 0
% 2.05/1.35  #Close   : 0
% 2.05/1.35  
% 2.05/1.35  Ordering : KBO
% 2.05/1.35  
% 2.05/1.35  Simplification rules
% 2.05/1.35  ----------------------
% 2.05/1.35  #Subsume      : 3
% 2.05/1.35  #Demod        : 3
% 2.05/1.35  #Tautology    : 5
% 2.05/1.35  #SimpNegUnit  : 0
% 2.05/1.35  #BackRed      : 0
% 2.05/1.35  
% 2.05/1.35  #Partial instantiations: 0
% 2.05/1.35  #Strategies tried      : 1
% 2.05/1.35  
% 2.05/1.35  Timing (in seconds)
% 2.05/1.35  ----------------------
% 2.05/1.35  Preprocessing        : 0.29
% 2.05/1.35  Parsing              : 0.16
% 2.05/1.35  CNF conversion       : 0.02
% 2.05/1.35  Main loop            : 0.24
% 2.05/1.35  Inferencing          : 0.11
% 2.05/1.35  Reduction            : 0.05
% 2.05/1.35  Demodulation         : 0.04
% 2.05/1.35  BG Simplification    : 0.01
% 2.05/1.35  Subsumption          : 0.04
% 2.05/1.35  Abstraction          : 0.01
% 2.05/1.35  MUC search           : 0.00
% 2.05/1.35  Cooper               : 0.00
% 2.05/1.35  Total                : 0.56
% 2.05/1.35  Index Insertion      : 0.00
% 2.05/1.35  Index Deletion       : 0.00
% 2.05/1.35  Index Matching       : 0.00
% 2.05/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

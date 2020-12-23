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
% DateTime   : Thu Dec  3 10:00:09 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
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
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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
           => r1_tarski(k5_relat_1(k8_relat_1(A,B),C),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k8_relat_1(A_6,B_7),B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

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
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(k5_relat_1(A_28,C_29),k5_relat_1(B_30,C_29))
      | ~ r1_tarski(A_28,B_30)
      | ~ v1_relat_1(C_29)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ~ r1_tarski(k5_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_3'),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_35,c_12])).

tff(c_44,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_38])).

tff(c_46,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_49,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_46])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_49])).

tff(c_54,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_58,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.13  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.13  
% 1.75/1.13  %Foreground sorts:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Background operators:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Foreground operators:
% 1.75/1.13  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.75/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.13  
% 1.75/1.14  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(k8_relat_1(A, B), C), k5_relat_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_relat_1)).
% 1.75/1.14  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.75/1.14  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.75/1.14  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.75/1.14  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relat_1)).
% 1.75/1.14  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.75/1.14  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k8_relat_1(A_6, B_7), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.75/1.14  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.14  tff(c_24, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.75/1.14  tff(c_29, plain, (![A_24, B_25]: (v1_relat_1(A_24) | ~v1_relat_1(B_25) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_4, c_24])).
% 1.75/1.14  tff(c_33, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_8, c_29])).
% 1.75/1.14  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.75/1.14  tff(c_35, plain, (![A_28, C_29, B_30]: (r1_tarski(k5_relat_1(A_28, C_29), k5_relat_1(B_30, C_29)) | ~r1_tarski(A_28, B_30) | ~v1_relat_1(C_29) | ~v1_relat_1(B_30) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.14  tff(c_12, plain, (~r1_tarski(k5_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.75/1.14  tff(c_38, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_35, c_12])).
% 1.75/1.14  tff(c_44, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_38])).
% 1.75/1.14  tff(c_46, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 1.75/1.14  tff(c_49, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_33, c_46])).
% 1.75/1.14  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_49])).
% 1.75/1.14  tff(c_54, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 1.75/1.14  tff(c_58, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_54])).
% 1.75/1.14  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 1.75/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  Inference rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Ref     : 0
% 1.75/1.14  #Sup     : 7
% 1.75/1.14  #Fact    : 0
% 1.75/1.14  #Define  : 0
% 1.75/1.14  #Split   : 1
% 1.75/1.14  #Chain   : 0
% 1.75/1.14  #Close   : 0
% 1.75/1.14  
% 1.75/1.14  Ordering : KBO
% 1.75/1.14  
% 1.75/1.14  Simplification rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Subsume      : 0
% 1.75/1.14  #Demod        : 4
% 1.75/1.14  #Tautology    : 1
% 1.75/1.14  #SimpNegUnit  : 0
% 1.75/1.14  #BackRed      : 0
% 1.75/1.14  
% 1.75/1.14  #Partial instantiations: 0
% 1.75/1.14  #Strategies tried      : 1
% 1.75/1.14  
% 1.75/1.14  Timing (in seconds)
% 1.75/1.14  ----------------------
% 1.75/1.15  Preprocessing        : 0.27
% 1.75/1.15  Parsing              : 0.15
% 1.75/1.15  CNF conversion       : 0.02
% 1.75/1.15  Main loop            : 0.11
% 1.75/1.15  Inferencing          : 0.05
% 1.75/1.15  Reduction            : 0.02
% 1.75/1.15  Demodulation         : 0.02
% 1.75/1.15  BG Simplification    : 0.01
% 1.75/1.15  Subsumption          : 0.02
% 1.75/1.15  Abstraction          : 0.00
% 1.75/1.15  MUC search           : 0.00
% 1.75/1.15  Cooper               : 0.00
% 1.75/1.15  Total                : 0.40
% 1.75/1.15  Index Insertion      : 0.00
% 1.75/1.15  Index Deletion       : 0.00
% 1.75/1.15  Index Matching       : 0.00
% 1.75/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

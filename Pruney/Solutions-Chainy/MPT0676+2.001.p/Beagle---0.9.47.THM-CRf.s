%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:24 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  79 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(k8_relat_1(A,C),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

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

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

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
    ! [B_18,A_19] :
      ( v1_relat_1(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_19))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_29,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(A_20)
      | ~ v1_relat_1(B_21)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_4,c_24])).

tff(c_33,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_35,plain,(
    ! [B_24,A_25,C_26] :
      ( r1_tarski(k9_relat_1(B_24,A_25),k9_relat_1(C_26,A_25))
      | ~ r1_tarski(B_24,C_26)
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_35,c_12])).

tff(c_44,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_46,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_49,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_46])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_49])).

tff(c_54,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_58,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:56:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.20  
% 1.85/1.20  %Foreground sorts:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Background operators:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Foreground operators:
% 1.85/1.20  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.85/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.85/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.20  
% 1.85/1.21  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(k8_relat_1(A, C), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_funct_1)).
% 1.85/1.21  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.85/1.21  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.85/1.21  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.85/1.21  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 1.85/1.21  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.85/1.21  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k8_relat_1(A_6, B_7), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.85/1.21  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.21  tff(c_24, plain, (![B_18, A_19]: (v1_relat_1(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_19)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.85/1.21  tff(c_29, plain, (![A_20, B_21]: (v1_relat_1(A_20) | ~v1_relat_1(B_21) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_4, c_24])).
% 1.85/1.21  tff(c_33, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_8, c_29])).
% 1.85/1.21  tff(c_35, plain, (![B_24, A_25, C_26]: (r1_tarski(k9_relat_1(B_24, A_25), k9_relat_1(C_26, A_25)) | ~r1_tarski(B_24, C_26) | ~v1_relat_1(C_26) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.21  tff(c_12, plain, (~r1_tarski(k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.85/1.21  tff(c_38, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_35, c_12])).
% 1.85/1.21  tff(c_44, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 1.85/1.21  tff(c_46, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 1.85/1.21  tff(c_49, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_33, c_46])).
% 1.85/1.21  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_49])).
% 1.85/1.21  tff(c_54, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 1.85/1.21  tff(c_58, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_54])).
% 1.85/1.21  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 1.85/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  Inference rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Ref     : 0
% 1.85/1.21  #Sup     : 7
% 1.85/1.21  #Fact    : 0
% 1.85/1.21  #Define  : 0
% 1.85/1.21  #Split   : 1
% 1.85/1.21  #Chain   : 0
% 1.85/1.21  #Close   : 0
% 1.85/1.21  
% 1.85/1.21  Ordering : KBO
% 1.85/1.21  
% 1.85/1.21  Simplification rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Subsume      : 0
% 1.85/1.21  #Demod        : 3
% 1.85/1.21  #Tautology    : 1
% 1.85/1.21  #SimpNegUnit  : 0
% 1.85/1.21  #BackRed      : 0
% 1.85/1.21  
% 1.85/1.21  #Partial instantiations: 0
% 1.85/1.21  #Strategies tried      : 1
% 1.85/1.21  
% 1.85/1.21  Timing (in seconds)
% 1.85/1.21  ----------------------
% 1.85/1.21  Preprocessing        : 0.29
% 1.85/1.21  Parsing              : 0.16
% 1.85/1.21  CNF conversion       : 0.02
% 1.85/1.21  Main loop            : 0.11
% 1.85/1.21  Inferencing          : 0.05
% 1.85/1.21  Reduction            : 0.03
% 1.85/1.21  Demodulation         : 0.02
% 1.85/1.21  BG Simplification    : 0.01
% 1.85/1.21  Subsumption          : 0.01
% 1.85/1.21  Abstraction          : 0.00
% 1.85/1.21  MUC search           : 0.00
% 1.85/1.21  Cooper               : 0.00
% 1.85/1.21  Total                : 0.42
% 1.85/1.21  Index Insertion      : 0.00
% 1.85/1.22  Index Deletion       : 0.00
% 1.85/1.22  Index Matching       : 0.00
% 1.85/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

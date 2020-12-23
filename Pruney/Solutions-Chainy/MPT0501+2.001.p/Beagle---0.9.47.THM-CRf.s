%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:47 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   33 (  48 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  75 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

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

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k7_relat_1(B_10,A_9),B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [B_17,A_18] :
      ( v1_relat_1(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_29,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(A_19)
      | ~ v1_relat_1(B_20)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_4,c_24])).

tff(c_33,plain,(
    ! [B_10,A_9] :
      ( v1_relat_1(k7_relat_1(B_10,A_9))
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_29])).

tff(c_40,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k2_relat_1(A_25),k2_relat_1(B_26))
      | ~ r1_tarski(A_25,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2','#skF_1')),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_14])).

tff(c_50,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_51,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_51])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_54])).

tff(c_59,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_63,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.43  
% 1.99/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.43  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
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
% 1.99/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.43  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.43  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.43  
% 1.99/1.45  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 1.99/1.45  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.99/1.45  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.45  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.99/1.45  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.99/1.45  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.45  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k7_relat_1(B_10, A_9), B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.45  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.45  tff(c_24, plain, (![B_17, A_18]: (v1_relat_1(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.99/1.45  tff(c_29, plain, (![A_19, B_20]: (v1_relat_1(A_19) | ~v1_relat_1(B_20) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_4, c_24])).
% 1.99/1.45  tff(c_33, plain, (![B_10, A_9]: (v1_relat_1(k7_relat_1(B_10, A_9)) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_12, c_29])).
% 1.99/1.45  tff(c_40, plain, (![A_25, B_26]: (r1_tarski(k2_relat_1(A_25), k2_relat_1(B_26)) | ~r1_tarski(A_25, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.45  tff(c_14, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', '#skF_1')), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.45  tff(c_46, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_14])).
% 1.99/1.45  tff(c_50, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46])).
% 1.99/1.45  tff(c_51, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 1.99/1.45  tff(c_54, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_33, c_51])).
% 1.99/1.45  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_54])).
% 1.99/1.45  tff(c_59, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 1.99/1.45  tff(c_63, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_59])).
% 1.99/1.45  tff(c_67, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_63])).
% 1.99/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.45  
% 1.99/1.45  Inference rules
% 1.99/1.45  ----------------------
% 1.99/1.45  #Ref     : 0
% 1.99/1.45  #Sup     : 8
% 1.99/1.45  #Fact    : 0
% 1.99/1.45  #Define  : 0
% 1.99/1.45  #Split   : 1
% 1.99/1.45  #Chain   : 0
% 1.99/1.45  #Close   : 0
% 1.99/1.45  
% 1.99/1.45  Ordering : KBO
% 1.99/1.45  
% 1.99/1.45  Simplification rules
% 1.99/1.45  ----------------------
% 1.99/1.45  #Subsume      : 0
% 1.99/1.45  #Demod        : 3
% 1.99/1.45  #Tautology    : 1
% 1.99/1.45  #SimpNegUnit  : 0
% 1.99/1.45  #BackRed      : 0
% 1.99/1.45  
% 1.99/1.45  #Partial instantiations: 0
% 1.99/1.45  #Strategies tried      : 1
% 1.99/1.45  
% 1.99/1.45  Timing (in seconds)
% 1.99/1.45  ----------------------
% 1.99/1.45  Preprocessing        : 0.42
% 1.99/1.45  Parsing              : 0.24
% 1.99/1.45  CNF conversion       : 0.03
% 1.99/1.45  Main loop            : 0.18
% 1.99/1.45  Inferencing          : 0.08
% 1.99/1.45  Reduction            : 0.04
% 1.99/1.45  Demodulation         : 0.03
% 1.99/1.46  BG Simplification    : 0.01
% 1.99/1.46  Subsumption          : 0.03
% 1.99/1.46  Abstraction          : 0.01
% 1.99/1.46  MUC search           : 0.00
% 1.99/1.46  Cooper               : 0.00
% 1.99/1.46  Total                : 0.65
% 1.99/1.46  Index Insertion      : 0.00
% 1.99/1.46  Index Deletion       : 0.00
% 1.99/1.46  Index Matching       : 0.00
% 1.99/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

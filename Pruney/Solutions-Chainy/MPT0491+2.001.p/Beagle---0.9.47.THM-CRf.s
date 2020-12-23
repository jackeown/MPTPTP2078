%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:35 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
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
       => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

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

tff(c_35,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_relat_1(A_23),k1_relat_1(B_24))
      | ~ r1_tarski(A_23,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_41,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_35,c_14])).

tff(c_45,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_41])).

tff(c_46,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_49,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_46])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_49])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_58,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_54])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.15  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.65/1.15  
% 1.65/1.15  %Foreground sorts:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Background operators:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Foreground operators:
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.15  
% 1.65/1.16  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 1.65/1.16  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.65/1.16  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.65/1.16  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.65/1.16  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.65/1.16  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.16  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k7_relat_1(B_10, A_9), B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.16  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.16  tff(c_24, plain, (![B_17, A_18]: (v1_relat_1(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.16  tff(c_29, plain, (![A_19, B_20]: (v1_relat_1(A_19) | ~v1_relat_1(B_20) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_4, c_24])).
% 1.65/1.16  tff(c_33, plain, (![B_10, A_9]: (v1_relat_1(k7_relat_1(B_10, A_9)) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_12, c_29])).
% 1.65/1.16  tff(c_35, plain, (![A_23, B_24]: (r1_tarski(k1_relat_1(A_23), k1_relat_1(B_24)) | ~r1_tarski(A_23, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.16  tff(c_14, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.16  tff(c_41, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_35, c_14])).
% 1.65/1.16  tff(c_45, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_41])).
% 1.65/1.16  tff(c_46, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_45])).
% 1.65/1.16  tff(c_49, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_33, c_46])).
% 1.65/1.16  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_49])).
% 1.65/1.16  tff(c_54, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_45])).
% 1.65/1.16  tff(c_58, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_54])).
% 1.65/1.16  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 1.65/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  Inference rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Ref     : 0
% 1.65/1.16  #Sup     : 7
% 1.65/1.16  #Fact    : 0
% 1.65/1.16  #Define  : 0
% 1.65/1.16  #Split   : 1
% 1.65/1.16  #Chain   : 0
% 1.65/1.16  #Close   : 0
% 1.65/1.16  
% 1.65/1.16  Ordering : KBO
% 1.65/1.16  
% 1.65/1.16  Simplification rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Subsume      : 0
% 1.65/1.16  #Demod        : 3
% 1.65/1.16  #Tautology    : 1
% 1.65/1.16  #SimpNegUnit  : 0
% 1.65/1.16  #BackRed      : 0
% 1.65/1.16  
% 1.65/1.16  #Partial instantiations: 0
% 1.65/1.16  #Strategies tried      : 1
% 1.65/1.16  
% 1.65/1.16  Timing (in seconds)
% 1.65/1.16  ----------------------
% 1.65/1.16  Preprocessing        : 0.24
% 1.65/1.16  Parsing              : 0.13
% 1.65/1.16  CNF conversion       : 0.02
% 1.65/1.16  Main loop            : 0.10
% 1.65/1.16  Inferencing          : 0.05
% 1.65/1.16  Reduction            : 0.02
% 1.65/1.16  Demodulation         : 0.02
% 1.65/1.16  BG Simplification    : 0.01
% 1.65/1.16  Subsumption          : 0.01
% 1.65/1.16  Abstraction          : 0.00
% 1.65/1.16  MUC search           : 0.00
% 1.65/1.16  Cooper               : 0.00
% 1.65/1.16  Total                : 0.37
% 1.65/1.16  Index Insertion      : 0.00
% 1.65/1.16  Index Deletion       : 0.00
% 1.65/1.16  Index Matching       : 0.00
% 1.65/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:00 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   36 (  70 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 141 expanded)
%              Number of equality atoms :    4 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(c_8,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_subset_1(A_12,k3_subset_1(A_12,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_90,plain,(
    ! [C_16,A_17,B_18] :
      ( r1_tarski(C_16,k3_subset_1(A_17,B_18))
      | ~ r1_tarski(B_18,k3_subset_1(A_17,C_16))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    ! [B_18] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',B_18))
      | ~ r1_tarski(B_18,'#skF_2')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_18,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_90])).

tff(c_97,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_100,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_106,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_10,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12,c_16])).

tff(c_96,plain,(
    ! [B_18] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1',B_18))
      | ~ r1_tarski(B_18,'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_18,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_130,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_133,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_133])).

tff(c_144,plain,(
    ! [B_20] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1',B_20))
      | ~ r1_tarski(B_20,'#skF_3')
      | ~ m1_subset_1(B_20,k1_zfmisc_1('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_153,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_144])).

tff(c_161,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_10,c_153])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n019.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 18:12:52 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  %$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.15  
% 1.68/1.15  %Foreground sorts:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Background operators:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Foreground operators:
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.15  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.15  
% 1.68/1.16  tff(f_52, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 1.68/1.16  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.68/1.16  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.68/1.16  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 1.68/1.16  tff(c_8, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.16  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.16  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.16  tff(c_16, plain, (![A_12, B_13]: (k3_subset_1(A_12, k3_subset_1(A_12, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.16  tff(c_25, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_14, c_16])).
% 1.68/1.16  tff(c_90, plain, (![C_16, A_17, B_18]: (r1_tarski(C_16, k3_subset_1(A_17, B_18)) | ~r1_tarski(B_18, k3_subset_1(A_17, C_16)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.16  tff(c_94, plain, (![B_18]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', B_18)) | ~r1_tarski(B_18, '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_18, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25, c_90])).
% 1.68/1.16  tff(c_97, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_94])).
% 1.68/1.16  tff(c_100, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_97])).
% 1.68/1.16  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_100])).
% 1.68/1.16  tff(c_106, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_94])).
% 1.68/1.16  tff(c_10, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.16  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.16  tff(c_24, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_12, c_16])).
% 1.68/1.16  tff(c_96, plain, (![B_18]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', B_18)) | ~r1_tarski(B_18, '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_18, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_90])).
% 1.68/1.16  tff(c_130, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_96])).
% 1.68/1.16  tff(c_133, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_130])).
% 1.68/1.16  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_133])).
% 1.68/1.16  tff(c_144, plain, (![B_20]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', B_20)) | ~r1_tarski(B_20, '#skF_3') | ~m1_subset_1(B_20, k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_96])).
% 1.68/1.16  tff(c_153, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_25, c_144])).
% 1.68/1.16  tff(c_161, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_10, c_153])).
% 1.68/1.16  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_161])).
% 1.68/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  Inference rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Ref     : 0
% 1.68/1.16  #Sup     : 35
% 1.68/1.16  #Fact    : 0
% 1.68/1.16  #Define  : 0
% 1.68/1.16  #Split   : 2
% 1.68/1.16  #Chain   : 0
% 1.68/1.16  #Close   : 0
% 1.68/1.16  
% 1.68/1.16  Ordering : KBO
% 1.68/1.16  
% 1.68/1.16  Simplification rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Subsume      : 2
% 1.68/1.16  #Demod        : 20
% 1.68/1.16  #Tautology    : 21
% 1.68/1.16  #SimpNegUnit  : 1
% 1.68/1.16  #BackRed      : 0
% 1.68/1.16  
% 1.68/1.16  #Partial instantiations: 0
% 1.68/1.16  #Strategies tried      : 1
% 1.68/1.16  
% 1.68/1.16  Timing (in seconds)
% 1.68/1.16  ----------------------
% 1.89/1.17  Preprocessing        : 0.26
% 1.89/1.17  Parsing              : 0.14
% 1.89/1.17  CNF conversion       : 0.02
% 1.89/1.17  Main loop            : 0.17
% 1.89/1.17  Inferencing          : 0.07
% 1.89/1.17  Reduction            : 0.05
% 1.89/1.17  Demodulation         : 0.04
% 1.89/1.17  BG Simplification    : 0.01
% 1.89/1.17  Subsumption          : 0.04
% 1.89/1.17  Abstraction          : 0.01
% 1.89/1.17  MUC search           : 0.00
% 1.89/1.17  Cooper               : 0.00
% 1.89/1.17  Total                : 0.46
% 1.89/1.17  Index Insertion      : 0.00
% 1.89/1.17  Index Deletion       : 0.00
% 1.89/1.17  Index Matching       : 0.00
% 1.89/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

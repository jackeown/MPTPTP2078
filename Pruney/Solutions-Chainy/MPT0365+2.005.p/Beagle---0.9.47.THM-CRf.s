%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:42 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 119 expanded)
%              Number of equality atoms :    5 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [B_8,A_7,C_10] :
      ( r1_tarski(B_8,k3_subset_1(A_7,C_10))
      | ~ r1_xboole_0(B_8,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_2])).

tff(c_54,plain,(
    ! [B_23,C_24,A_25] :
      ( r1_tarski(B_23,C_24)
      | ~ r1_xboole_0(B_23,k3_subset_1(A_25,C_24))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_41,c_54])).

tff(c_63,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_57])).

tff(c_94,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_152,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_152])).

tff(c_157,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,
    ( k3_subset_1('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_157,c_4])).

tff(c_202,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_199])).

tff(c_206,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.19  
% 1.90/1.19  %Foreground sorts:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Background operators:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Foreground operators:
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.19  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.90/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.19  
% 2.02/1.20  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 2.02/1.20  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.02/1.20  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.02/1.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.02/1.20  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.02/1.20  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.02/1.20  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.20  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.20  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.20  tff(c_14, plain, (![B_8, A_7, C_10]: (r1_tarski(B_8, k3_subset_1(A_7, C_10)) | ~r1_xboole_0(B_8, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.20  tff(c_20, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.20  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.20  tff(c_22, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.20  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.20  tff(c_41, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_2])).
% 2.02/1.20  tff(c_54, plain, (![B_23, C_24, A_25]: (r1_tarski(B_23, C_24) | ~r1_xboole_0(B_23, k3_subset_1(A_25, C_24)) | ~m1_subset_1(C_24, k1_zfmisc_1(A_25)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.20  tff(c_57, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_41, c_54])).
% 2.02/1.20  tff(c_63, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_57])).
% 2.02/1.20  tff(c_94, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_63])).
% 2.02/1.20  tff(c_152, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_94])).
% 2.02/1.20  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_152])).
% 2.02/1.20  tff(c_157, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_63])).
% 2.02/1.20  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.20  tff(c_199, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_157, c_4])).
% 2.02/1.20  tff(c_202, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_20, c_199])).
% 2.02/1.20  tff(c_206, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_202])).
% 2.02/1.20  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_206])).
% 2.02/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.20  
% 2.02/1.20  Inference rules
% 2.02/1.20  ----------------------
% 2.02/1.20  #Ref     : 0
% 2.02/1.20  #Sup     : 33
% 2.02/1.20  #Fact    : 0
% 2.02/1.20  #Define  : 0
% 2.02/1.20  #Split   : 3
% 2.02/1.20  #Chain   : 0
% 2.02/1.20  #Close   : 0
% 2.02/1.20  
% 2.02/1.20  Ordering : KBO
% 2.02/1.20  
% 2.02/1.20  Simplification rules
% 2.02/1.20  ----------------------
% 2.02/1.20  #Subsume      : 0
% 2.02/1.20  #Demod        : 47
% 2.02/1.20  #Tautology    : 23
% 2.02/1.20  #SimpNegUnit  : 1
% 2.02/1.20  #BackRed      : 8
% 2.02/1.20  
% 2.02/1.20  #Partial instantiations: 0
% 2.02/1.20  #Strategies tried      : 1
% 2.02/1.20  
% 2.02/1.20  Timing (in seconds)
% 2.02/1.20  ----------------------
% 2.02/1.21  Preprocessing        : 0.28
% 2.02/1.21  Parsing              : 0.15
% 2.02/1.21  CNF conversion       : 0.02
% 2.02/1.21  Main loop            : 0.18
% 2.02/1.21  Inferencing          : 0.06
% 2.02/1.21  Reduction            : 0.06
% 2.02/1.21  Demodulation         : 0.04
% 2.02/1.21  BG Simplification    : 0.01
% 2.02/1.21  Subsumption          : 0.04
% 2.02/1.21  Abstraction          : 0.01
% 2.02/1.21  MUC search           : 0.00
% 2.02/1.21  Cooper               : 0.00
% 2.02/1.21  Total                : 0.48
% 2.02/1.21  Index Insertion      : 0.00
% 2.02/1.21  Index Deletion       : 0.00
% 2.02/1.21  Index Matching       : 0.00
% 2.02/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:06 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  33 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_39,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( k3_subset_1(A,B) = k3_subset_1(A,C)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_4,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15,plain,(
    ! [A_4,B_5] :
      ( k3_subset_1(A_4,k3_subset_1(A_4,B_5)) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_15])).

tff(c_6,plain,(
    k3_subset_1('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_22,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19])).

tff(c_27,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_28,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.14  
% 1.55/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.14  %$ m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.55/1.14  
% 1.55/1.14  %Foreground sorts:
% 1.55/1.14  
% 1.55/1.14  
% 1.55/1.14  %Background operators:
% 1.55/1.14  
% 1.55/1.14  
% 1.55/1.14  %Foreground operators:
% 1.55/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.55/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.55/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.55/1.14  
% 1.55/1.15  tff(f_39, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((k3_subset_1(A, B) = k3_subset_1(A, C)) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_subset_1)).
% 1.55/1.15  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.55/1.15  tff(c_4, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.15  tff(c_8, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.15  tff(c_15, plain, (![A_4, B_5]: (k3_subset_1(A_4, k3_subset_1(A_4, B_5))=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.15  tff(c_20, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_8, c_15])).
% 1.55/1.15  tff(c_6, plain, (k3_subset_1('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.15  tff(c_10, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.15  tff(c_19, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_10, c_15])).
% 1.55/1.15  tff(c_22, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_19])).
% 1.55/1.15  tff(c_27, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 1.55/1.15  tff(c_28, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_27])).
% 1.55/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.15  
% 1.55/1.15  Inference rules
% 1.55/1.15  ----------------------
% 1.55/1.15  #Ref     : 0
% 1.55/1.15  #Sup     : 6
% 1.55/1.15  #Fact    : 0
% 1.55/1.15  #Define  : 0
% 1.55/1.15  #Split   : 0
% 1.55/1.15  #Chain   : 0
% 1.55/1.15  #Close   : 0
% 1.55/1.15  
% 1.55/1.15  Ordering : KBO
% 1.55/1.15  
% 1.55/1.15  Simplification rules
% 1.55/1.15  ----------------------
% 1.55/1.15  #Subsume      : 0
% 1.55/1.15  #Demod        : 2
% 1.55/1.15  #Tautology    : 4
% 1.55/1.15  #SimpNegUnit  : 1
% 1.55/1.15  #BackRed      : 0
% 1.55/1.15  
% 1.55/1.15  #Partial instantiations: 0
% 1.55/1.15  #Strategies tried      : 1
% 1.55/1.15  
% 1.55/1.15  Timing (in seconds)
% 1.55/1.15  ----------------------
% 1.55/1.15  Preprocessing        : 0.27
% 1.55/1.15  Parsing              : 0.15
% 1.55/1.15  CNF conversion       : 0.01
% 1.55/1.15  Main loop            : 0.06
% 1.55/1.15  Inferencing          : 0.02
% 1.55/1.15  Reduction            : 0.02
% 1.55/1.15  Demodulation         : 0.01
% 1.55/1.15  BG Simplification    : 0.01
% 1.55/1.15  Subsumption          : 0.01
% 1.55/1.16  Abstraction          : 0.00
% 1.55/1.16  MUC search           : 0.00
% 1.55/1.16  Cooper               : 0.00
% 1.55/1.16  Total                : 0.35
% 1.55/1.16  Index Insertion      : 0.00
% 1.55/1.16  Index Deletion       : 0.00
% 1.55/1.16  Index Matching       : 0.00
% 1.55/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

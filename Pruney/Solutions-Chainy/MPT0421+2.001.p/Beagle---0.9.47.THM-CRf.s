%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:52 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
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
%$ m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( k7_setfam_1(A,B) = k7_setfam_1(A,C)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_4,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15,plain,(
    ! [A_4,B_5] :
      ( k7_setfam_1(A_4,k7_setfam_1(A_4,B_5)) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_15])).

tff(c_6,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k7_setfam_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_22,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19])).

tff(c_27,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_28,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 20:51:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.06  
% 1.48/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.06  %$ m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.48/1.06  
% 1.48/1.06  %Foreground sorts:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Background operators:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Foreground operators:
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.06  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.48/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.48/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.48/1.06  
% 1.48/1.07  tff(f_39, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((k7_setfam_1(A, B) = k7_setfam_1(A, C)) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_setfam_1)).
% 1.48/1.07  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 1.48/1.07  tff(c_4, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.48/1.07  tff(c_8, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.48/1.07  tff(c_15, plain, (![A_4, B_5]: (k7_setfam_1(A_4, k7_setfam_1(A_4, B_5))=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.07  tff(c_20, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_8, c_15])).
% 1.48/1.07  tff(c_6, plain, (k7_setfam_1('#skF_1', '#skF_2')=k7_setfam_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.48/1.07  tff(c_10, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.48/1.07  tff(c_19, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_10, c_15])).
% 1.48/1.07  tff(c_22, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_19])).
% 1.48/1.07  tff(c_27, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 1.48/1.07  tff(c_28, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_27])).
% 1.48/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.07  
% 1.48/1.07  Inference rules
% 1.48/1.07  ----------------------
% 1.48/1.07  #Ref     : 0
% 1.48/1.07  #Sup     : 6
% 1.48/1.07  #Fact    : 0
% 1.48/1.07  #Define  : 0
% 1.48/1.07  #Split   : 0
% 1.48/1.07  #Chain   : 0
% 1.48/1.07  #Close   : 0
% 1.48/1.07  
% 1.48/1.07  Ordering : KBO
% 1.48/1.07  
% 1.48/1.07  Simplification rules
% 1.48/1.07  ----------------------
% 1.48/1.07  #Subsume      : 0
% 1.48/1.07  #Demod        : 2
% 1.48/1.07  #Tautology    : 4
% 1.48/1.07  #SimpNegUnit  : 1
% 1.48/1.07  #BackRed      : 0
% 1.48/1.07  
% 1.48/1.07  #Partial instantiations: 0
% 1.48/1.07  #Strategies tried      : 1
% 1.48/1.07  
% 1.48/1.07  Timing (in seconds)
% 1.48/1.07  ----------------------
% 1.48/1.07  Preprocessing        : 0.25
% 1.48/1.07  Parsing              : 0.13
% 1.48/1.07  CNF conversion       : 0.01
% 1.48/1.07  Main loop            : 0.06
% 1.48/1.07  Inferencing          : 0.03
% 1.48/1.07  Reduction            : 0.02
% 1.48/1.07  Demodulation         : 0.01
% 1.48/1.07  BG Simplification    : 0.01
% 1.48/1.07  Subsumption          : 0.01
% 1.48/1.07  Abstraction          : 0.00
% 1.48/1.07  MUC search           : 0.00
% 1.48/1.07  Cooper               : 0.00
% 1.48/1.07  Total                : 0.34
% 1.48/1.07  Index Insertion      : 0.00
% 1.48/1.07  Index Deletion       : 0.00
% 1.48/1.07  Index Matching       : 0.00
% 1.48/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

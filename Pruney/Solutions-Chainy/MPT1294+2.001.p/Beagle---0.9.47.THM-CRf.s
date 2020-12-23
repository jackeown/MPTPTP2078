%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:38 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 ( 114 expanded)
%              Number of equality atoms :   23 (  72 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(c_18,plain,
    ( k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_2'
    | k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    k7_setfam_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_24])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(k7_setfam_1(A_23,B_24),C_25)
      | ~ r1_tarski(B_24,k7_setfam_1(A_23,C_25))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_zfmisc_1(A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [B_26] :
      ( r1_tarski(k7_setfam_1('#skF_1',B_26),'#skF_2')
      | ~ r1_tarski(B_26,k7_setfam_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_79,plain,
    ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_82,plain,(
    r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_79])).

tff(c_37,plain,(
    ! [B_13,A_14] :
      ( B_13 = A_14
      | ~ r1_tarski(B_13,A_14)
      | ~ r1_tarski(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_29,c_37])).

tff(c_87,plain,(
    k7_setfam_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_82,c_42])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_87])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_97,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_115,plain,(
    ! [A_29,B_30] :
      ( k7_setfam_1(A_29,B_30) != k1_xboole_0
      | k1_xboole_0 = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_115])).

tff(c_121,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_118])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  %$ r1_tarski > m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.12  
% 1.60/1.12  %Foreground sorts:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Background operators:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Foreground operators:
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.12  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.60/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.60/1.12  
% 1.60/1.13  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tops_2)).
% 1.60/1.13  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.60/1.13  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_setfam_1)).
% 1.60/1.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.60/1.13  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 1.60/1.13  tff(c_18, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.60/1.13  tff(c_28, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_18])).
% 1.60/1.13  tff(c_24, plain, (k1_xboole_0!='#skF_2' | k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.60/1.13  tff(c_36, plain, (k7_setfam_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_24])).
% 1.60/1.13  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.13  tff(c_29, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8])).
% 1.60/1.13  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.60/1.13  tff(c_72, plain, (![A_23, B_24, C_25]: (r1_tarski(k7_setfam_1(A_23, B_24), C_25) | ~r1_tarski(B_24, k7_setfam_1(A_23, C_25)) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_zfmisc_1(A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.60/1.13  tff(c_76, plain, (![B_26]: (r1_tarski(k7_setfam_1('#skF_1', B_26), '#skF_2') | ~r1_tarski(B_26, k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_16, c_72])).
% 1.60/1.13  tff(c_79, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_76])).
% 1.60/1.13  tff(c_82, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_79])).
% 1.60/1.13  tff(c_37, plain, (![B_13, A_14]: (B_13=A_14 | ~r1_tarski(B_13, A_14) | ~r1_tarski(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.13  tff(c_42, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(resolution, [status(thm)], [c_29, c_37])).
% 1.60/1.13  tff(c_87, plain, (k7_setfam_1('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_82, c_42])).
% 1.60/1.13  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_87])).
% 1.60/1.13  tff(c_98, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_18])).
% 1.60/1.13  tff(c_97, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.60/1.13  tff(c_115, plain, (![A_29, B_30]: (k7_setfam_1(A_29, B_30)!=k1_xboole_0 | k1_xboole_0=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.60/1.13  tff(c_118, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_16, c_115])).
% 1.60/1.13  tff(c_121, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_118])).
% 1.60/1.13  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_121])).
% 1.60/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  
% 1.60/1.13  Inference rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Ref     : 0
% 1.60/1.13  #Sup     : 18
% 1.60/1.13  #Fact    : 0
% 1.60/1.13  #Define  : 0
% 1.60/1.13  #Split   : 1
% 1.60/1.13  #Chain   : 0
% 1.60/1.13  #Close   : 0
% 1.60/1.13  
% 1.60/1.13  Ordering : KBO
% 1.60/1.13  
% 1.60/1.13  Simplification rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Subsume      : 2
% 1.60/1.13  #Demod        : 13
% 1.60/1.13  #Tautology    : 12
% 1.60/1.13  #SimpNegUnit  : 2
% 1.60/1.13  #BackRed      : 1
% 1.60/1.13  
% 1.60/1.13  #Partial instantiations: 0
% 1.60/1.13  #Strategies tried      : 1
% 1.60/1.13  
% 1.60/1.13  Timing (in seconds)
% 1.60/1.13  ----------------------
% 1.60/1.13  Preprocessing        : 0.26
% 1.60/1.13  Parsing              : 0.14
% 1.60/1.13  CNF conversion       : 0.02
% 1.60/1.13  Main loop            : 0.11
% 1.60/1.13  Inferencing          : 0.04
% 1.60/1.13  Reduction            : 0.03
% 1.60/1.13  Demodulation         : 0.02
% 1.60/1.13  BG Simplification    : 0.01
% 1.60/1.13  Subsumption          : 0.02
% 1.60/1.13  Abstraction          : 0.01
% 1.60/1.13  MUC search           : 0.00
% 1.60/1.13  Cooper               : 0.00
% 1.60/1.13  Total                : 0.40
% 1.60/1.13  Index Insertion      : 0.00
% 1.60/1.13  Index Deletion       : 0.00
% 1.60/1.13  Index Matching       : 0.00
% 1.60/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

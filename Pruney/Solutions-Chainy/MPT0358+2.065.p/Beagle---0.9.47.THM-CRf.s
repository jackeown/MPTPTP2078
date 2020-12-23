%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:08 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   39 (  83 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 ( 116 expanded)
%              Number of equality atoms :   22 (  63 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_10,plain,(
    ! [A_6] : k1_subset_1(A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,
    ( k1_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_62,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_23])).

tff(c_22,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_24])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_5] : k4_xboole_0('#skF_2',A_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_67,c_66])).

tff(c_95,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_23])).

tff(c_96,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_23])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k3_subset_1(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_119,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_6])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_123])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.62/1.12  
% 1.62/1.12  %Foreground sorts:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Background operators:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Foreground operators:
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.12  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.62/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.12  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.62/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.62/1.12  
% 1.62/1.13  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.62/1.13  tff(f_48, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 1.62/1.13  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.62/1.13  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.62/1.13  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.62/1.13  tff(f_33, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.62/1.13  tff(c_10, plain, (![A_6]: (k1_subset_1(A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.13  tff(c_16, plain, (k1_subset_1('#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.13  tff(c_23, plain, (k1_xboole_0!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 1.62/1.13  tff(c_62, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_23])).
% 1.62/1.13  tff(c_22, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.13  tff(c_24, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 1.62/1.13  tff(c_67, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_24])).
% 1.62/1.13  tff(c_8, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.13  tff(c_72, plain, (![A_5]: (k4_xboole_0('#skF_2', A_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_8])).
% 1.62/1.13  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.13  tff(c_66, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_62])).
% 1.62/1.13  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_67, c_66])).
% 1.62/1.13  tff(c_95, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_23])).
% 1.62/1.13  tff(c_96, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_23])).
% 1.62/1.13  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.13  tff(c_115, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k3_subset_1(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.13  tff(c_119, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_115])).
% 1.62/1.13  tff(c_6, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k4_xboole_0(B_4, A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.13  tff(c_123, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_6])).
% 1.62/1.13  tff(c_127, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_123])).
% 1.62/1.13  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_127])).
% 1.62/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  Inference rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Ref     : 0
% 1.62/1.13  #Sup     : 24
% 1.62/1.13  #Fact    : 0
% 1.62/1.13  #Define  : 0
% 1.62/1.13  #Split   : 1
% 1.62/1.13  #Chain   : 0
% 1.62/1.13  #Close   : 0
% 1.62/1.13  
% 1.62/1.13  Ordering : KBO
% 1.62/1.13  
% 1.62/1.13  Simplification rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Subsume      : 1
% 1.62/1.13  #Demod        : 16
% 1.62/1.13  #Tautology    : 18
% 1.62/1.13  #SimpNegUnit  : 3
% 1.62/1.13  #BackRed      : 6
% 1.62/1.13  
% 1.62/1.13  #Partial instantiations: 0
% 1.62/1.13  #Strategies tried      : 1
% 1.62/1.13  
% 1.62/1.13  Timing (in seconds)
% 1.62/1.13  ----------------------
% 1.62/1.14  Preprocessing        : 0.27
% 1.62/1.14  Parsing              : 0.15
% 1.62/1.14  CNF conversion       : 0.02
% 1.62/1.14  Main loop            : 0.11
% 1.62/1.14  Inferencing          : 0.04
% 1.62/1.14  Reduction            : 0.03
% 1.62/1.14  Demodulation         : 0.02
% 1.62/1.14  BG Simplification    : 0.01
% 1.62/1.14  Subsumption          : 0.02
% 1.62/1.14  Abstraction          : 0.01
% 1.62/1.14  MUC search           : 0.00
% 1.62/1.14  Cooper               : 0.00
% 1.62/1.14  Total                : 0.40
% 1.62/1.14  Index Insertion      : 0.00
% 1.62/1.14  Index Deletion       : 0.00
% 1.62/1.14  Index Matching       : 0.00
% 1.62/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

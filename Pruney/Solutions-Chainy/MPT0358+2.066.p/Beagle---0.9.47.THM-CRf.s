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
% DateTime   : Thu Dec  3 09:56:08 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   42 (  62 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  79 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_14,plain,(
    ! [A_8] : k1_subset_1(A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,
    ( k1_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_27,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_43,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_27])).

tff(c_26,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_28])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_43])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_65,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_98,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k3_subset_1(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [A_30] :
      ( r1_xboole_0(A_30,'#skF_2')
      | ~ r1_tarski(A_30,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_132,plain,(
    r1_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_124])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.14  
% 1.77/1.14  %Foreground sorts:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Background operators:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Foreground operators:
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.77/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.77/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.14  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.77/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.14  
% 1.77/1.15  tff(f_49, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.77/1.15  tff(f_60, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 1.77/1.15  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.77/1.15  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.77/1.15  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.77/1.15  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.77/1.15  tff(c_14, plain, (![A_8]: (k1_subset_1(A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.77/1.15  tff(c_20, plain, (k1_subset_1('#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.77/1.15  tff(c_27, plain, (k1_xboole_0!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 1.77/1.15  tff(c_43, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_27])).
% 1.77/1.15  tff(c_26, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.77/1.15  tff(c_28, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 1.77/1.15  tff(c_44, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_43, c_28])).
% 1.77/1.15  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.15  tff(c_47, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 1.77/1.15  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_43])).
% 1.77/1.15  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_27])).
% 1.77/1.15  tff(c_65, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_27])).
% 1.77/1.15  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.77/1.15  tff(c_98, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k3_subset_1(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.77/1.15  tff(c_102, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_98])).
% 1.77/1.15  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.15  tff(c_124, plain, (![A_30]: (r1_xboole_0(A_30, '#skF_2') | ~r1_tarski(A_30, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 1.77/1.15  tff(c_132, plain, (r1_xboole_0('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_65, c_124])).
% 1.77/1.15  tff(c_12, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.15  tff(c_137, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_132, c_12])).
% 1.77/1.15  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_137])).
% 1.77/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  Inference rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Ref     : 0
% 1.77/1.15  #Sup     : 22
% 1.77/1.15  #Fact    : 0
% 1.77/1.15  #Define  : 0
% 1.77/1.15  #Split   : 1
% 1.77/1.15  #Chain   : 0
% 1.77/1.15  #Close   : 0
% 1.77/1.15  
% 1.77/1.15  Ordering : KBO
% 1.77/1.15  
% 1.77/1.15  Simplification rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Subsume      : 0
% 1.77/1.15  #Demod        : 13
% 1.77/1.15  #Tautology    : 19
% 1.77/1.15  #SimpNegUnit  : 3
% 1.77/1.15  #BackRed      : 5
% 1.77/1.15  
% 1.77/1.15  #Partial instantiations: 0
% 1.77/1.15  #Strategies tried      : 1
% 1.77/1.15  
% 1.77/1.15  Timing (in seconds)
% 1.77/1.15  ----------------------
% 1.77/1.15  Preprocessing        : 0.28
% 1.77/1.15  Parsing              : 0.15
% 1.77/1.15  CNF conversion       : 0.02
% 1.77/1.15  Main loop            : 0.11
% 1.77/1.15  Inferencing          : 0.04
% 1.77/1.15  Reduction            : 0.04
% 1.77/1.15  Demodulation         : 0.03
% 1.77/1.15  BG Simplification    : 0.01
% 1.77/1.15  Subsumption          : 0.01
% 1.77/1.15  Abstraction          : 0.01
% 1.77/1.15  MUC search           : 0.00
% 1.77/1.15  Cooper               : 0.00
% 1.77/1.15  Total                : 0.41
% 1.77/1.15  Index Insertion      : 0.00
% 1.77/1.15  Index Deletion       : 0.00
% 1.77/1.15  Index Matching       : 0.00
% 1.77/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:25 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  73 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_11,B_49] :
      ( r2_hidden('#skF_3'(A_11),B_49)
      | ~ r1_tarski(A_11,B_49)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_26,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_107,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k3_subset_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_111,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_107])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,k4_xboole_0(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_146,plain,(
    ! [A_60] :
      ( r1_xboole_0(A_60,'#skF_6')
      | ~ r1_tarski(A_60,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_18])).

tff(c_167,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_171,plain,(
    ! [C_61] :
      ( ~ r2_hidden(C_61,'#skF_6')
      | ~ r2_hidden(C_61,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_191,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_198,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_191])).

tff(c_201,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_99,c_198])).

tff(c_204,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_201])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.00/1.21  
% 2.00/1.21  %Foreground sorts:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Background operators:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Foreground operators:
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.21  tff('#skF_6', type, '#skF_6': $i).
% 2.00/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.21  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.21  
% 2.00/1.22  tff(f_79, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.00/1.22  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.00/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.00/1.22  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.00/1.22  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.00/1.22  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.00/1.22  tff(c_24, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.22  tff(c_28, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.22  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.22  tff(c_87, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.22  tff(c_99, plain, (![A_11, B_49]: (r2_hidden('#skF_3'(A_11), B_49) | ~r1_tarski(A_11, B_49) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_87])).
% 2.00/1.22  tff(c_26, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.22  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.22  tff(c_107, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k3_subset_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.00/1.22  tff(c_111, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_30, c_107])).
% 2.00/1.22  tff(c_18, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.22  tff(c_146, plain, (![A_60]: (r1_xboole_0(A_60, '#skF_6') | ~r1_tarski(A_60, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_18])).
% 2.00/1.22  tff(c_167, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_146])).
% 2.00/1.22  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.22  tff(c_171, plain, (![C_61]: (~r2_hidden(C_61, '#skF_6') | ~r2_hidden(C_61, '#skF_5'))), inference(resolution, [status(thm)], [c_167, c_8])).
% 2.00/1.22  tff(c_191, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_6') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_14, c_171])).
% 2.00/1.22  tff(c_198, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_24, c_191])).
% 2.00/1.22  tff(c_201, plain, (~r1_tarski('#skF_5', '#skF_6') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_99, c_198])).
% 2.00/1.22  tff(c_204, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_201])).
% 2.00/1.22  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_204])).
% 2.00/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  Inference rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Ref     : 0
% 2.00/1.22  #Sup     : 38
% 2.00/1.22  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 0
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 0
% 2.00/1.23  #Demod        : 3
% 2.00/1.23  #Tautology    : 6
% 2.00/1.23  #SimpNegUnit  : 2
% 2.00/1.23  #BackRed      : 0
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.30
% 2.00/1.23  Parsing              : 0.16
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.17
% 2.00/1.23  Inferencing          : 0.07
% 2.00/1.23  Reduction            : 0.05
% 2.00/1.23  Demodulation         : 0.04
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.23  Subsumption          : 0.03
% 2.00/1.23  Abstraction          : 0.01
% 2.00/1.23  MUC search           : 0.00
% 2.00/1.23  Cooper               : 0.00
% 2.00/1.23  Total                : 0.50
% 2.00/1.23  Index Insertion      : 0.00
% 2.00/1.23  Index Deletion       : 0.00
% 2.00/1.23  Index Matching       : 0.00
% 2.00/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

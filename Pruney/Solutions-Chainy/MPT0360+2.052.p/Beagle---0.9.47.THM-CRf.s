%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:25 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  76 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [C_35,B_36,A_37] :
      ( r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_11,B_36] :
      ( r2_hidden('#skF_3'(A_11),B_36)
      | ~ r1_tarski(A_11,B_36)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_64])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_86,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_39,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,B_30)
      | ~ r2_hidden(C_31,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ! [C_31,B_14,A_13] :
      ( ~ r2_hidden(C_31,B_14)
      | ~ r2_hidden(C_31,k4_xboole_0(A_13,B_14)) ) ),
    inference(resolution,[status(thm)],[c_16,c_39])).

tff(c_104,plain,(
    ! [C_42] :
      ( ~ r2_hidden(C_42,'#skF_6')
      | ~ r2_hidden(C_42,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_42])).

tff(c_184,plain,(
    ! [A_53] :
      ( ~ r2_hidden('#skF_3'(A_53),'#skF_6')
      | ~ r1_tarski(A_53,k3_subset_1('#skF_4','#skF_6'))
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_76,c_104])).

tff(c_196,plain,(
    ! [A_54] :
      ( ~ r1_tarski(A_54,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_54,'#skF_6')
      | k1_xboole_0 = A_54 ) ),
    inference(resolution,[status(thm)],[c_76,c_184])).

tff(c_203,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_196])).

tff(c_207,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_203])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.21  
% 1.78/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.78/1.22  
% 1.78/1.22  %Foreground sorts:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Background operators:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Foreground operators:
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.78/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.78/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.78/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.78/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.22  
% 2.00/1.23  tff(f_73, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.00/1.23  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.00/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.00/1.23  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.00/1.23  tff(f_60, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.00/1.23  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.00/1.23  tff(c_20, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.00/1.23  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.00/1.23  tff(c_22, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.00/1.23  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.23  tff(c_64, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.23  tff(c_76, plain, (![A_11, B_36]: (r2_hidden('#skF_3'(A_11), B_36) | ~r1_tarski(A_11, B_36) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_64])).
% 2.00/1.23  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.00/1.23  tff(c_86, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.23  tff(c_90, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_86])).
% 2.00/1.23  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.00/1.23  tff(c_39, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, B_30) | ~r2_hidden(C_31, A_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.23  tff(c_42, plain, (![C_31, B_14, A_13]: (~r2_hidden(C_31, B_14) | ~r2_hidden(C_31, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_16, c_39])).
% 2.00/1.23  tff(c_104, plain, (![C_42]: (~r2_hidden(C_42, '#skF_6') | ~r2_hidden(C_42, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_42])).
% 2.00/1.23  tff(c_184, plain, (![A_53]: (~r2_hidden('#skF_3'(A_53), '#skF_6') | ~r1_tarski(A_53, k3_subset_1('#skF_4', '#skF_6')) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_76, c_104])).
% 2.00/1.23  tff(c_196, plain, (![A_54]: (~r1_tarski(A_54, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_54, '#skF_6') | k1_xboole_0=A_54)), inference(resolution, [status(thm)], [c_76, c_184])).
% 2.00/1.23  tff(c_203, plain, (~r1_tarski('#skF_5', '#skF_6') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_196])).
% 2.00/1.23  tff(c_207, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_203])).
% 2.00/1.23  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_207])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 38
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 3
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 4
% 2.00/1.23  #Demod        : 3
% 2.00/1.23  #Tautology    : 3
% 2.00/1.23  #SimpNegUnit  : 1
% 2.00/1.23  #BackRed      : 0
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.27
% 2.00/1.23  Parsing              : 0.14
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.17
% 2.00/1.23  Inferencing          : 0.07
% 2.00/1.23  Reduction            : 0.04
% 2.00/1.23  Demodulation         : 0.03
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.23  Subsumption          : 0.04
% 2.00/1.23  Abstraction          : 0.01
% 2.00/1.23  MUC search           : 0.00
% 2.00/1.23  Cooper               : 0.00
% 2.00/1.23  Total                : 0.47
% 2.00/1.23  Index Insertion      : 0.00
% 2.00/1.23  Index Deletion       : 0.00
% 2.00/1.23  Index Matching       : 0.00
% 2.00/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

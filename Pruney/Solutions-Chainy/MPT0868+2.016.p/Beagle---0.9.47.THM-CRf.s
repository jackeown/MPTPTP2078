%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:25 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   35 (  82 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 192 expanded)
%              Number of equality atoms :   40 ( 160 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_15,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [C_15,A_16,B_17] :
      ( k4_tarski(k1_mcart_1(C_15),k2_mcart_1(C_15)) = C_15
      | ~ m1_subset_1(C_15,k2_zfmisc_1(A_16,B_17))
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_26,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_24])).

tff(c_27,plain,(
    k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_26])).

tff(c_4,plain,(
    ! [B_4,C_5] : k1_mcart_1(k4_tarski(B_4,C_5)) != k4_tarski(B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_31,plain,(
    k4_tarski('#skF_3',k2_mcart_1('#skF_3')) != k1_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_15,c_31])).

tff(c_40,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_48,plain,(
    ! [C_22,A_23,B_24] :
      ( k4_tarski(k1_mcart_1(C_22),k2_mcart_1(C_22)) = C_22
      | ~ m1_subset_1(C_22,k2_zfmisc_1(A_23,B_24))
      | k1_xboole_0 = B_24
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_52,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_50])).

tff(c_53,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_52])).

tff(c_2,plain,(
    ! [B_4,C_5] : k2_mcart_1(k4_tarski(B_4,C_5)) != k4_tarski(B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_57,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') != k2_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_40,c_57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.34  
% 2.00/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.35  %$ m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.35  
% 2.00/1.35  %Foreground sorts:
% 2.00/1.35  
% 2.00/1.35  
% 2.00/1.35  %Background operators:
% 2.00/1.35  
% 2.00/1.35  
% 2.00/1.35  %Foreground operators:
% 2.00/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.35  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.00/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.35  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.00/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.35  
% 2.00/1.36  tff(f_65, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.00/1.36  tff(f_47, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.00/1.36  tff(f_34, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.00/1.36  tff(c_14, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.36  tff(c_12, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.36  tff(c_8, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.36  tff(c_15, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_8])).
% 2.00/1.36  tff(c_10, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.36  tff(c_22, plain, (![C_15, A_16, B_17]: (k4_tarski(k1_mcart_1(C_15), k2_mcart_1(C_15))=C_15 | ~m1_subset_1(C_15, k2_zfmisc_1(A_16, B_17)) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.36  tff(c_24, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_10, c_22])).
% 2.00/1.36  tff(c_26, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15, c_24])).
% 2.00/1.36  tff(c_27, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14, c_12, c_26])).
% 2.00/1.36  tff(c_4, plain, (![B_4, C_5]: (k1_mcart_1(k4_tarski(B_4, C_5))!=k4_tarski(B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.36  tff(c_31, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))!=k1_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27, c_4])).
% 2.00/1.36  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_15, c_31])).
% 2.00/1.36  tff(c_40, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_8])).
% 2.00/1.36  tff(c_48, plain, (![C_22, A_23, B_24]: (k4_tarski(k1_mcart_1(C_22), k2_mcart_1(C_22))=C_22 | ~m1_subset_1(C_22, k2_zfmisc_1(A_23, B_24)) | k1_xboole_0=B_24 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.36  tff(c_50, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_10, c_48])).
% 2.00/1.36  tff(c_52, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_50])).
% 2.00/1.36  tff(c_53, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14, c_12, c_52])).
% 2.00/1.36  tff(c_2, plain, (![B_4, C_5]: (k2_mcart_1(k4_tarski(B_4, C_5))!=k4_tarski(B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.36  tff(c_57, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')!=k2_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_53, c_2])).
% 2.00/1.36  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_40, c_57])).
% 2.00/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.36  
% 2.00/1.36  Inference rules
% 2.00/1.36  ----------------------
% 2.00/1.36  #Ref     : 0
% 2.00/1.36  #Sup     : 14
% 2.00/1.36  #Fact    : 0
% 2.00/1.36  #Define  : 0
% 2.00/1.36  #Split   : 1
% 2.00/1.36  #Chain   : 0
% 2.00/1.36  #Close   : 0
% 2.00/1.36  
% 2.00/1.36  Ordering : KBO
% 2.00/1.36  
% 2.00/1.36  Simplification rules
% 2.00/1.36  ----------------------
% 2.00/1.36  #Subsume      : 0
% 2.00/1.36  #Demod        : 6
% 2.00/1.36  #Tautology    : 6
% 2.00/1.36  #SimpNegUnit  : 2
% 2.00/1.36  #BackRed      : 0
% 2.00/1.36  
% 2.00/1.36  #Partial instantiations: 0
% 2.04/1.36  #Strategies tried      : 1
% 2.04/1.36  
% 2.04/1.36  Timing (in seconds)
% 2.04/1.36  ----------------------
% 2.04/1.37  Preprocessing        : 0.44
% 2.04/1.37  Parsing              : 0.23
% 2.04/1.37  CNF conversion       : 0.03
% 2.04/1.37  Main loop            : 0.14
% 2.04/1.37  Inferencing          : 0.05
% 2.04/1.37  Reduction            : 0.04
% 2.04/1.37  Demodulation         : 0.03
% 2.04/1.37  BG Simplification    : 0.01
% 2.04/1.37  Subsumption          : 0.02
% 2.04/1.37  Abstraction          : 0.01
% 2.04/1.37  MUC search           : 0.00
% 2.04/1.37  Cooper               : 0.00
% 2.04/1.37  Total                : 0.62
% 2.04/1.37  Index Insertion      : 0.00
% 2.04/1.37  Index Deletion       : 0.00
% 2.04/1.37  Index Matching       : 0.00
% 2.04/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

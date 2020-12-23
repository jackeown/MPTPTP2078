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
% DateTime   : Thu Dec  3 09:50:32 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   27 (  51 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   36 ( 112 expanded)
%              Number of equality atoms :   35 ( 111 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(c_24,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [B_6,A_7,C_8] :
      ( k1_xboole_0 = B_6
      | k1_tarski(A_7) = B_6
      | k2_xboole_0(B_6,C_8) != k1_tarski(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_7] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_7) = '#skF_2'
      | k1_tarski(A_7) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_40])).

tff(c_44,plain,(
    ! [A_7] :
      ( k1_tarski(A_7) = '#skF_2'
      | k1_tarski(A_7) != k1_tarski('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_43])).

tff(c_47,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_44])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_26])).

tff(c_63,plain,(
    ! [A_10,C_11,B_12] :
      ( k1_tarski(A_10) = C_11
      | k1_xboole_0 = C_11
      | k2_xboole_0(B_12,C_11) != k1_tarski(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    ! [A_10] :
      ( k1_tarski(A_10) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k1_tarski(A_10) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_63])).

tff(c_68,plain,(
    ! [A_13] :
      ( k1_tarski(A_13) = '#skF_3'
      | k1_tarski(A_13) != '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_66])).

tff(c_72,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_68])).

tff(c_73,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_47])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.11  %$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.62/1.11  
% 1.62/1.11  %Foreground sorts:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Background operators:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Foreground operators:
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.11  
% 1.70/1.12  tff(f_58, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.70/1.12  tff(f_45, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 1.70/1.12  tff(c_24, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.12  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.12  tff(c_26, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.12  tff(c_40, plain, (![B_6, A_7, C_8]: (k1_xboole_0=B_6 | k1_tarski(A_7)=B_6 | k2_xboole_0(B_6, C_8)!=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.12  tff(c_43, plain, (![A_7]: (k1_xboole_0='#skF_2' | k1_tarski(A_7)='#skF_2' | k1_tarski(A_7)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_40])).
% 1.70/1.12  tff(c_44, plain, (![A_7]: (k1_tarski(A_7)='#skF_2' | k1_tarski(A_7)!=k1_tarski('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_22, c_43])).
% 1.70/1.12  tff(c_47, plain, (k1_tarski('#skF_1')='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_44])).
% 1.70/1.12  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.12  tff(c_50, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_26])).
% 1.70/1.12  tff(c_63, plain, (![A_10, C_11, B_12]: (k1_tarski(A_10)=C_11 | k1_xboole_0=C_11 | k2_xboole_0(B_12, C_11)!=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.12  tff(c_66, plain, (![A_10]: (k1_tarski(A_10)='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski(A_10)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50, c_63])).
% 1.70/1.12  tff(c_68, plain, (![A_13]: (k1_tarski(A_13)='#skF_3' | k1_tarski(A_13)!='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_66])).
% 1.70/1.12  tff(c_72, plain, (k1_tarski('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_47, c_68])).
% 1.70/1.12  tff(c_73, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_47])).
% 1.70/1.12  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_73])).
% 1.70/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  Inference rules
% 1.70/1.12  ----------------------
% 1.70/1.12  #Ref     : 1
% 1.70/1.12  #Sup     : 12
% 1.70/1.12  #Fact    : 0
% 1.70/1.12  #Define  : 0
% 1.70/1.12  #Split   : 0
% 1.70/1.12  #Chain   : 0
% 1.70/1.12  #Close   : 0
% 1.70/1.12  
% 1.70/1.12  Ordering : KBO
% 1.70/1.12  
% 1.70/1.12  Simplification rules
% 1.70/1.12  ----------------------
% 1.70/1.12  #Subsume      : 5
% 1.70/1.12  #Demod        : 3
% 1.70/1.12  #Tautology    : 10
% 1.70/1.12  #SimpNegUnit  : 4
% 1.70/1.12  #BackRed      : 2
% 1.70/1.12  
% 1.70/1.12  #Partial instantiations: 0
% 1.70/1.12  #Strategies tried      : 1
% 1.70/1.12  
% 1.70/1.12  Timing (in seconds)
% 1.70/1.12  ----------------------
% 1.70/1.12  Preprocessing        : 0.25
% 1.70/1.12  Parsing              : 0.12
% 1.70/1.13  CNF conversion       : 0.01
% 1.70/1.13  Main loop            : 0.09
% 1.70/1.13  Inferencing          : 0.03
% 1.70/1.13  Reduction            : 0.02
% 1.70/1.13  Demodulation         : 0.01
% 1.70/1.13  BG Simplification    : 0.01
% 1.70/1.13  Subsumption          : 0.02
% 1.70/1.13  Abstraction          : 0.00
% 1.70/1.13  MUC search           : 0.00
% 1.70/1.13  Cooper               : 0.00
% 1.70/1.13  Total                : 0.36
% 1.70/1.13  Index Insertion      : 0.00
% 1.70/1.13  Index Deletion       : 0.00
% 1.70/1.13  Index Matching       : 0.00
% 1.70/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

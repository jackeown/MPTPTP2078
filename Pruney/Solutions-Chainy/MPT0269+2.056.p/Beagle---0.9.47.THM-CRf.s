%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:51 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  38 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_14,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,k1_tarski(B_18)) = A_17
      | r2_hidden(B_18,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_18])).

tff(c_101,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_88])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(k1_tarski(A_4),B_5) = k1_xboole_0
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [B_15,A_16] :
      ( B_15 = A_16
      | k4_xboole_0(B_15,A_16) != k4_xboole_0(A_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    ! [A_19,B_20] :
      ( k1_tarski(A_19) = B_20
      | k4_xboole_0(B_20,k1_tarski(A_19)) != k1_xboole_0
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_115,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_105])).

tff(c_119,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_115])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  %$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.79/1.19  
% 1.79/1.19  %Foreground sorts:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Background operators:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Foreground operators:
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.19  
% 1.79/1.20  tff(f_50, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.79/1.20  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.79/1.20  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.79/1.20  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 1.79/1.20  tff(c_14, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.20  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.20  tff(c_65, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k1_tarski(B_18))=A_17 | r2_hidden(B_18, A_17))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.20  tff(c_18, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.20  tff(c_88, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_18])).
% 1.79/1.20  tff(c_101, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16, c_88])).
% 1.79/1.20  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(k1_tarski(A_4), B_5)=k1_xboole_0 | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.20  tff(c_58, plain, (![B_15, A_16]: (B_15=A_16 | k4_xboole_0(B_15, A_16)!=k4_xboole_0(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.20  tff(c_105, plain, (![A_19, B_20]: (k1_tarski(A_19)=B_20 | k4_xboole_0(B_20, k1_tarski(A_19))!=k1_xboole_0 | ~r2_hidden(A_19, B_20))), inference(superposition, [status(thm), theory('equality')], [c_8, c_58])).
% 1.79/1.20  tff(c_115, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_105])).
% 1.79/1.20  tff(c_119, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_115])).
% 1.79/1.20  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_119])).
% 1.79/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  Inference rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Ref     : 1
% 1.79/1.20  #Sup     : 24
% 1.79/1.20  #Fact    : 0
% 1.79/1.20  #Define  : 0
% 1.79/1.20  #Split   : 0
% 1.79/1.20  #Chain   : 0
% 1.79/1.20  #Close   : 0
% 1.79/1.20  
% 1.79/1.20  Ordering : KBO
% 1.79/1.20  
% 1.79/1.20  Simplification rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Subsume      : 1
% 1.79/1.20  #Demod        : 2
% 1.79/1.20  #Tautology    : 13
% 1.79/1.20  #SimpNegUnit  : 3
% 1.79/1.20  #BackRed      : 0
% 1.79/1.20  
% 1.79/1.20  #Partial instantiations: 0
% 1.79/1.20  #Strategies tried      : 1
% 1.79/1.20  
% 1.79/1.20  Timing (in seconds)
% 1.79/1.20  ----------------------
% 1.79/1.20  Preprocessing        : 0.30
% 1.79/1.20  Parsing              : 0.16
% 1.79/1.20  CNF conversion       : 0.02
% 1.79/1.20  Main loop            : 0.10
% 1.79/1.20  Inferencing          : 0.04
% 1.79/1.20  Reduction            : 0.03
% 1.79/1.20  Demodulation         : 0.02
% 1.79/1.20  BG Simplification    : 0.01
% 1.79/1.20  Subsumption          : 0.02
% 1.79/1.20  Abstraction          : 0.01
% 1.79/1.20  MUC search           : 0.00
% 1.79/1.20  Cooper               : 0.00
% 1.79/1.20  Total                : 0.42
% 1.79/1.20  Index Insertion      : 0.00
% 1.79/1.20  Index Deletion       : 0.00
% 1.79/1.20  Index Matching       : 0.00
% 1.79/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

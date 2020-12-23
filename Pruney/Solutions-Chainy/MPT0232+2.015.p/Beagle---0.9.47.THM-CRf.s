%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:21 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k1_tarski(A_7),k2_tarski(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [C_18,A_19,B_20] :
      ( C_18 = A_19
      | ~ r1_tarski(k2_tarski(A_19,B_20),k1_tarski(C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_50])).

tff(c_16,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    ! [B_16,A_17] :
      ( B_16 = A_17
      | ~ r1_tarski(B_16,A_17)
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_44,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_37])).

tff(c_58,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_44])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:47:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.17  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.66/1.17  
% 1.66/1.17  %Foreground sorts:
% 1.66/1.17  
% 1.66/1.17  
% 1.66/1.17  %Background operators:
% 1.66/1.17  
% 1.66/1.17  
% 1.66/1.17  %Foreground operators:
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.17  
% 1.66/1.18  tff(f_41, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.66/1.18  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 1.66/1.18  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.66/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.66/1.18  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), k2_tarski(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.66/1.18  tff(c_18, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.66/1.18  tff(c_50, plain, (![C_18, A_19, B_20]: (C_18=A_19 | ~r1_tarski(k2_tarski(A_19, B_20), k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.18  tff(c_57, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_18, c_50])).
% 1.66/1.18  tff(c_16, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.66/1.18  tff(c_35, plain, (![B_16, A_17]: (B_16=A_17 | ~r1_tarski(B_16, A_17) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.18  tff(c_37, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | ~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_35])).
% 1.66/1.18  tff(c_44, plain, (~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_16, c_37])).
% 1.66/1.18  tff(c_58, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_44])).
% 1.66/1.18  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_58])).
% 1.66/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.18  
% 1.66/1.18  Inference rules
% 1.66/1.18  ----------------------
% 1.66/1.18  #Ref     : 0
% 1.66/1.18  #Sup     : 8
% 1.66/1.18  #Fact    : 0
% 1.66/1.18  #Define  : 0
% 1.66/1.18  #Split   : 0
% 1.66/1.18  #Chain   : 0
% 1.66/1.18  #Close   : 0
% 1.66/1.18  
% 1.66/1.18  Ordering : KBO
% 1.66/1.18  
% 1.66/1.18  Simplification rules
% 1.66/1.18  ----------------------
% 1.66/1.18  #Subsume      : 0
% 1.66/1.18  #Demod        : 7
% 1.66/1.18  #Tautology    : 5
% 1.66/1.18  #SimpNegUnit  : 1
% 1.66/1.18  #BackRed      : 3
% 1.66/1.18  
% 1.66/1.18  #Partial instantiations: 0
% 1.66/1.18  #Strategies tried      : 1
% 1.66/1.18  
% 1.66/1.18  Timing (in seconds)
% 1.66/1.18  ----------------------
% 1.66/1.18  Preprocessing        : 0.27
% 1.66/1.18  Parsing              : 0.15
% 1.66/1.18  CNF conversion       : 0.02
% 1.66/1.18  Main loop            : 0.08
% 1.66/1.18  Inferencing          : 0.03
% 1.66/1.18  Reduction            : 0.03
% 1.66/1.18  Demodulation         : 0.02
% 1.66/1.18  BG Simplification    : 0.01
% 1.66/1.18  Subsumption          : 0.01
% 1.66/1.18  Abstraction          : 0.00
% 1.66/1.18  MUC search           : 0.00
% 1.66/1.18  Cooper               : 0.00
% 1.66/1.18  Total                : 0.37
% 1.66/1.18  Index Insertion      : 0.00
% 1.66/1.18  Index Deletion       : 0.00
% 1.66/1.18  Index Matching       : 0.00
% 1.66/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

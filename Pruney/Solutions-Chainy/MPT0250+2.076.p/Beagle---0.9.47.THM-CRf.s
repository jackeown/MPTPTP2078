%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:41 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  51 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_180,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_180])).

tff(c_284,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_287,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_287])).

tff(c_292,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_99,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(A_60,C_61)
      | ~ r1_tarski(k2_tarski(A_60,B_62),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_123,plain,(
    ! [A_66,C_67] :
      ( r2_hidden(A_66,C_67)
      | ~ r1_tarski(k1_tarski(A_66),C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_99])).

tff(c_137,plain,(
    ! [A_66,B_7] : r2_hidden(A_66,k2_xboole_0(k1_tarski(A_66),B_7)) ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_305,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_137])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:18:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.10/1.27  
% 2.10/1.27  %Foreground sorts:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Background operators:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Foreground operators:
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.27  
% 2.10/1.28  tff(f_68, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.10/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.28  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.10/1.28  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.10/1.28  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.10/1.28  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.10/1.28  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.28  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.28  tff(c_40, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.28  tff(c_180, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.28  tff(c_190, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_180])).
% 2.10/1.28  tff(c_284, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_190])).
% 2.10/1.28  tff(c_287, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_284])).
% 2.10/1.28  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_287])).
% 2.10/1.28  tff(c_292, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_190])).
% 2.10/1.28  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.28  tff(c_18, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.28  tff(c_99, plain, (![A_60, C_61, B_62]: (r2_hidden(A_60, C_61) | ~r1_tarski(k2_tarski(A_60, B_62), C_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.28  tff(c_123, plain, (![A_66, C_67]: (r2_hidden(A_66, C_67) | ~r1_tarski(k1_tarski(A_66), C_67))), inference(superposition, [status(thm), theory('equality')], [c_18, c_99])).
% 2.10/1.28  tff(c_137, plain, (![A_66, B_7]: (r2_hidden(A_66, k2_xboole_0(k1_tarski(A_66), B_7)))), inference(resolution, [status(thm)], [c_10, c_123])).
% 2.10/1.28  tff(c_305, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_292, c_137])).
% 2.10/1.28  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_305])).
% 2.10/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  Inference rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Ref     : 0
% 2.10/1.28  #Sup     : 59
% 2.10/1.28  #Fact    : 0
% 2.10/1.28  #Define  : 0
% 2.10/1.28  #Split   : 1
% 2.10/1.28  #Chain   : 0
% 2.10/1.28  #Close   : 0
% 2.10/1.28  
% 2.10/1.28  Ordering : KBO
% 2.10/1.28  
% 2.10/1.28  Simplification rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Subsume      : 2
% 2.10/1.28  #Demod        : 16
% 2.10/1.28  #Tautology    : 27
% 2.10/1.28  #SimpNegUnit  : 1
% 2.10/1.28  #BackRed      : 1
% 2.10/1.28  
% 2.10/1.28  #Partial instantiations: 0
% 2.10/1.28  #Strategies tried      : 1
% 2.10/1.28  
% 2.10/1.28  Timing (in seconds)
% 2.10/1.28  ----------------------
% 2.10/1.28  Preprocessing        : 0.31
% 2.10/1.28  Parsing              : 0.17
% 2.10/1.28  CNF conversion       : 0.02
% 2.10/1.28  Main loop            : 0.19
% 2.10/1.28  Inferencing          : 0.07
% 2.10/1.28  Reduction            : 0.07
% 2.10/1.28  Demodulation         : 0.05
% 2.10/1.28  BG Simplification    : 0.02
% 2.10/1.28  Subsumption          : 0.04
% 2.10/1.28  Abstraction          : 0.01
% 2.10/1.28  MUC search           : 0.00
% 2.10/1.28  Cooper               : 0.00
% 2.10/1.28  Total                : 0.53
% 2.10/1.28  Index Insertion      : 0.00
% 2.10/1.28  Index Deletion       : 0.00
% 2.10/1.28  Index Matching       : 0.00
% 2.10/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
